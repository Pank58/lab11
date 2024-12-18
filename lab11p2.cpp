#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <Windows.h>
#include <locale.h>

struct node {
	int vertex;
	struct node* next;
};

struct Noode {
	int* marking; // Текущая маркировка
	int* transitionSequence; // Последовательность переходов для этой маркировки
	int* transitionVariants; // Доступность переходов занчение 1 или 0
	int transitionCount; // Количество переходов
	struct Noode** next; // Указатель на следующие узелы
	struct Noode* prev; // Указатель на предыдущее состояние
};

struct visit_node
{
	int* marking;
	struct visit_node* next;
};

void addNode(struct node** head, int vertex) {
	struct node* newNode = (struct node*)malloc(sizeof(struct node));
	newNode->vertex = vertex;
	newNode->next = *head;   // Добавляем в начало списка
	*head = newNode;
}

void printReachabilityTree(struct Noode* node, int depth, int t, int p) {
	if (node == NULL) return;

	// Вывод информации о текущем узле с отступами
	for (int i = 0; i < depth; i++) {
		printf("  "); // Отступ для визуализации уровня
	}
	for (int i = 0; i < p; i++) { 
		printf("%d ", node->marking[i]);
	}
	printf("\n");

	// Рекурсивный вызов для всех следующих узлов
	for (int j = 0; j < t; j++) {
		printReachabilityTree(node->next[j], depth + 1, t, p);
	}
}

void FindMar(struct Noode* node, int *marking, int t, int p, int* controlfind) {
	if (node == NULL || *controlfind==1) return;
	int checkmar = 0;

	for (int i = 0; i < p; i++) { 
		if (marking[i] == node->marking[i]) {
			checkmar++;
		}
	}
	
	if (checkmar == p) {
		printf("\n\n");
		printf("Маркировка: ");
		for (int i = 0; i < p; i++) {
			printf("%d ", node->marking[i]);
		}
		printf("\tДостижимость: %d", node->transitionCount);
		printf("\nпоследовательность преходов: ");
		for (int i = 0; i < node->transitionCount; i++) {
			printf("%d ", node->transitionSequence[i]);
		}
		*controlfind = 1;
		return;
	}
	else {
		for (int j = 0; j < t; j++) {
			FindMar(node->next[j], marking, t, p, controlfind);
		}
	}
}

int isVisited(visit_node* head, int* marking, int p) {
	struct visit_node* current = head;
	while (current != NULL) {
		int same = 1;
		for (int i = 0; i < p; i++) {
			if (current->marking[i] != marking[i]) {
				same = 0;
				break;
			}
		}
		if (same) {
			return 1; // Состояние уже посещено
		}
		current = current->next;
	}
	return 0;
}

void addVisit(struct visit_node** head, int* marking, int p) {
	struct visit_node* newNode = (struct visit_node*)malloc(sizeof(struct visit_node));
	newNode->marking = (int*)malloc(p * sizeof(int));
	for (int i = 0; i < p; i++) {
		newNode->marking[i] = marking[i];
	}

	newNode->next = *head;
	*head = newNode;
}

bool isAccumulated(int* currentMarking, int* previousMarking, int p) {
	int diffCount = 0;
	for (int i = 0; i < p; i++) {
		if (currentMarking[i] - previousMarking[i] == 1) {
			diffCount++;
		}
		else if (currentMarking[i] != previousMarking[i]) {
			return false; // Если разница не равна 1, возвращаем false
		}
	}
	return diffCount == 1; // Если разница только в одной вершине, возвращаем true
}

void createReachabilityTree(struct Noode* currentNode, int** UnityMatrix, int* MarkVector, int p, int t,
	int* chekLimitations, int ControlLimitations, int* chekConerv, int ControlConerv, int* chekconsistent, visit_node** visited, int* control, int* controlnacop) {
	// Сохраняем текущую маркировку в узле
	int localmark = 0;

	if (isVisited(*visited, MarkVector, p)) {
		*control = 1;
		return;
	}

	addVisit(visited, MarkVector, p);

	for (int i = 0; i < p; i++) {
		currentNode->marking[i] = MarkVector[i];
	}

	for (int i = 0; i < p; i++) {
		if (MarkVector[i] > ControlLimitations) {
			*chekLimitations = 0;
		}
	}

	for (int i = 0; i < p; i++) {
		localmark += MarkVector[i];
	}

	if (localmark != ControlConerv) {
		*chekConerv = 0;
	}


	// Инициализация доступности переходов
	currentNode->transitionVariants = (int*)malloc(t * sizeof(int));
	for (int j = 0; j < t; j++) {
		// Проверяем, можем ли выполнить переход j
		bool canFire = true;
		for (int i = 0; i < p; i++) {
			if (MarkVector[i] + UnityMatrix[i][j] < 0) {
				canFire = false;
				break;
			}
		}
		int pr = chekconsistent[j];
		currentNode->transitionVariants[j] = canFire ? 1 : 0; // 1 - доступен, 0 - недоступен
		chekconsistent[j] = canFire ? 1 : pr;
	}


	// Перебираем все переходы
	for (int j = 0; j < t; j++) {
		if (currentNode->transitionVariants[j] == 1) {
			// Создаем новый узел
			struct Noode* newNode = (struct Noode*)malloc(sizeof(struct Noode));
			newNode->marking = (int*)malloc(p * sizeof(int));
			newNode->next = (struct Noode**)malloc(t * sizeof(struct Noode*));
			newNode->prev = currentNode;
			newNode->transitionCount = currentNode->transitionCount + 1;
			newNode->transitionSequence = (int*)malloc((newNode->transitionCount) * sizeof(int));

			// Сохраняем последовательность переходов
			for (int k = 0; k < currentNode->transitionCount; k++) {
				newNode->transitionSequence[k] = currentNode->transitionSequence[k];
			}
			newNode->transitionSequence[currentNode->transitionCount] = j; // Сохраняем индекс перехода

			// Обновляем маркировку
			for (int i = 0; i < p; i++) {
				MarkVector[i] += UnityMatrix[i][j]; // Обновляем маркировку
			}

			bool wasAccumulatedLastTime = false; // Переменная для отслеживания предыдущего состояния накопляемости

			if (currentNode->prev != NULL) {
				if (isAccumulated(MarkVector, currentNode->marking, p) && isAccumulated(currentNode->marking, currentNode->prev->marking, p)) {
					free(newNode->marking);
					free(newNode->next);
					free(newNode->transitionSequence);
					free(newNode);
					currentNode->next[j] = NULL;
					*controlnacop = 1;

				}
				else {

					createReachabilityTree(newNode, UnityMatrix, MarkVector, p, t, chekLimitations, ControlLimitations, chekConerv, ControlConerv, chekconsistent, visited, control, controlnacop);

					if (*control == 0) {
						currentNode->next[j] = newNode;
					}
					else {
						currentNode->next[j] = NULL;
						*control = 0;
					}


				}
			}
			else {
				createReachabilityTree(newNode, UnityMatrix, MarkVector, p, t, chekLimitations, ControlLimitations, chekConerv, ControlConerv, chekconsistent, visited, control, controlnacop);

				if (*control == 0) {
					currentNode->next[j] = newNode;
				}
				else {
					currentNode->next[j] = NULL;
					*control = 0;
				}

			}

			// Восстанавливаем маркировку для следующего перехода
			for (int i = 0; i < p; i++) {
				MarkVector[i] -= UnityMatrix[i][j]; // Восстанавливаем маркировку
			}
		}
		else {
			currentNode->next[j] = NULL;
		}
	}
}


void generateWebPetry(int p, int t) {
	int a;

	struct node** inputFunctions = (struct node**)malloc(t * sizeof(struct node*));

	for (int i = 0; i < t; i++) {
		inputFunctions[i] = NULL;
		printf("Введите количество входов для перехода %d: ", i);
		int count;
		scanf("%d", &count);

		for (int k = 0; k < count; k++) {
			int vertex;
			printf("Введите номер позиции: ", k + 1);
			scanf("%d", &vertex);
			addNode(&inputFunctions[i], vertex);
		}
	}


	struct node** outputFunctions = (struct node**)malloc(t * sizeof(struct node*));

	for (int i = 0; i < t; i++) {
		outputFunctions[i] = NULL;
		printf("Введите количество выходов для перехода %d: ", i);
		int count;
		scanf("%d", &count);

		for (int k = 0; k < count; k++) {
			int vertex;
			printf("Введите номер позиции: ", k + 1);
			scanf("%d", &vertex);
			addNode(&outputFunctions[i], vertex);
		}
	}

	for (int i = 0; i < t; i++) {
		printf("I(t%d) = ", i);
		struct node* current = inputFunctions[i];
		printf("(");
		while (current != NULL) {
			printf("p%d", current->vertex);
			current = current->next;
			if (current != NULL) {
				printf(", ");
			}
		}
		printf(")");
		printf("\n");
	}


	for (int i = 0; i < t; i++) {
		printf("O(t%d) = ", i);
		struct node* current = outputFunctions[i];
		printf("(");
		while (current != NULL) {
			printf("p%d", current->vertex);
			current = current->next;
			if (current != NULL) {
				printf(", ");
			}
		}
		printf(")");
		printf("\n");
	}

	int** inputMatrix = (int**)malloc(p * sizeof(int*));
	for (int i = 0; i < p; i++) {
		inputMatrix[i] = (int*)malloc(t * sizeof(int));
	}

	for (int j = 0; j < t; j++) {
		for (int i = 0; i < p; i++) {
			inputMatrix[i][j] = 0;
		}
	}

	for (int i = 0; i < t; i++) {
		struct node* current = inputFunctions[i];
		while (current != NULL) {
			if (current->vertex < p) {
				inputMatrix[current->vertex][i]++;
			}
			current = current->next;
		}
	}

	int** outputMatrix = (int**)malloc(p * sizeof(int*));
	for (int i = 0; i < p; i++) {
		outputMatrix[i] = (int*)malloc(t * sizeof(int));
	}


	for (int j = 0; j < t; j++) {
		for (int i = 0; i < p; i++) {
			outputMatrix[i][j] = 0;
		}
	}

	for (int i = 0; i < t; i++) {
		struct node* current = outputFunctions[i];
		while (current != NULL) {
			if (current->vertex < p) {
				outputMatrix[current->vertex][i]++;
			}
			current = current->next;
		}
	}


	printf("Матрица входов сети:\n");
	for (int i = 0; i < p; i++) {
		for (int j = 0; j < t; j++) {
			printf("%d ", inputMatrix[i][j]);
		}
		printf("\n");
	}

	printf("Матрица выходов сети:\n");
	for (int i = 0; i < p; i++) {
		for (int j = 0; j < t; j++) {
			printf("%d ", outputMatrix[i][j]);
		}
		printf("\n");
	}

	int* MarkVector = (int*)malloc(p * sizeof(int));
	for (int i = 0; i < p; i++) {
		printf("Введите фишки позиции %d сети ", i);
		scanf("%d", &a);
		MarkVector[i] = a;
	}


	int** UnityMatrix = (int**)malloc(p * sizeof(int*));
	for (int i = 0; i < p; i++) {
		UnityMatrix[i] = (int*)malloc(t * sizeof(int));
	}

	for (int i = 0; i < p; i++) {
		for (int j = 0; j < t; j++) {
			UnityMatrix[i][j] = outputMatrix[i][j] - inputMatrix[i][j];
		}
	}

	printf("вектор начальной маркировоки: ");
	for (int i = 0; i < p; i++) {
		printf("%d, ", MarkVector[i]);
	}
	printf("\n");

	printf("Матрица изменения маркировок:\n");
	for (int i = 0; i < p; i++) {
		for (int j = 0; j < t; j++) {
			printf("%d ", UnityMatrix[i][j]);
		}
		printf("\n");
	}

	struct Noode* root = (struct Noode*)malloc(sizeof(struct Noode));
	root->marking = (int*)malloc(p * sizeof(int));
	root->next = (struct Noode**)malloc(t * sizeof(struct Noode*));
	root->prev = NULL;
	root->transitionCount = 0;
	root->transitionSequence = NULL; // Изначально нет переходов

	int chekLimitations = 1;
	int ControlLimitations = 0;

	int chekConerv = 1;
	int ControlConerv = 0;

	int* chekconsistent = (int*)malloc(t * sizeof(int));
	for (int i = 0; i < t; i++) {
		chekconsistent[i] = 0; // Сохраняем начальную маркировку в корневом узле
	}


	for (int i = 0; i < p; i++) {
		ControlConerv += MarkVector[i];
	}

	// Инициализация вектора маркировки
	for (int i = 0; i < p; i++) {
		root->marking[i] = MarkVector[i]; // Сохраняем начальную маркировку в корневом узле
	}

	printf("введите число на проверку ограниченности");
	scanf("%d", &ControlLimitations);

	struct visit_node* visited = NULL;
	int control = 0;
	int controlnacop = 0;

	// Создание дерева достижимости
	createReachabilityTree(root, UnityMatrix, MarkVector, p, t, &chekLimitations, ControlLimitations, &chekConerv, ControlConerv, chekconsistent, &visited, &control, &controlnacop);

	printReachabilityTree(root, 0, t, p);

	if (chekLimitations == 1) {
		printf("ограничена по %d", ControlLimitations);
	}
	else {
		printf("не ораничена по %d", ControlLimitations);
	}

	printf("\n");

	if (chekConerv == 1) {
		printf("сеть консервативна");
	}
	else {
		printf("сеть не консервативна");
	}


	printf("\n");

	int chekall = 0;
	for (int i = 0; i < t; i++) {
		chekall += chekconsistent[i]; // Сохраняем начальную маркировку в корневом узле
	}
	if (chekall == t) {
		printf("сеть непротиворечива");
	}
	else {
		printf("сеть противоречива");
	}
	printf("\n");
	if (controlnacop == 1) {
		printf("сеть повторяема");
	}
	else {
		printf("сеть не повторяема");
	}
	printf("\n\n");

	int controlfind = 0;
	printf("Введите необходимую марикровку");
	int* FindMarkVector = (int*)malloc(p * sizeof(int));
	for (int i = 0; i < p; i++) {
		printf("Введите фишки позиции %d сети ", i);
		scanf("%d", &a);
		FindMarkVector[i] = a;
	}

	FindMar(root, FindMarkVector, t, p, &controlfind);
	if (controlfind == 0) {
		printf("Такой марикровки нет");
	}
}

int main() {

	setlocale(LC_ALL, "");

	int p, t;
	printf("Введите количество позиций сети: ");
	scanf("%d", &p);
	printf("Введите количество переходов сети: ");
	scanf("%d", &t);

	generateWebPetry(p, t);

	return 0;
}
