-- Prove2me | solution 1 for CLRS.Chapter4RecursionTree.recurrence_tree_accounting
-- status  : ACCEPTED   (prove)
-- author  : @Chutong
-- created : 2026-10-11T06:34:29.565522+00:00
-- url     : https://prove2.me/submissions/f38201e8-13df-4b69-b28a-de629f8750f4

import Definitions.Def_CLRS_Chapter4_RecursionTree
import Definitions.Def_CLRS_Chapter4_Substitution
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section
namespace CLRS

/-!
Generic finite recursion-tree accounting. Branching factors and child heights
may differ at every node. Work is a mathematical natural-number charge attached
to a call; these theorems do not assume a balanced or fixed-arity call tree.
-/

namespace Chapter4RecursionTree

















theorem sumBelow_shift (count : Nat) (f : Nat → Nat) :
    sumBelow (count+1) f = f 0 + sumBelow count (fun i => f (i+1)) := by
  induction count with
  | zero => simp [sumBelow]
  | succ count ih => simp only [sumBelow] at ih ⊢; omega

theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega



@[simp] theorem sum_map_zero {α : Type} (xs : List α) : (xs.map (fun _ => (0:Nat))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-- Interchange two finite sums; no convergence assumption is needed. -/
theorem sumBelow_map_sum {α : Type} (count : Nat) (xs : List α) (f : α → Nat → Nat) :
    sumBelow count (fun i => (xs.map (fun x => f x i)).sum) =
      (xs.map (fun x => sumBelow count (f x))).sum := by
  induction count with
  | zero => simp [sumBelow]
  | succ count ih =>
    simp only [sumBelow, ih, sum_map_add]







theorem le_foldr_max (xs : List Nat) (value : Nat) (member : value ∈ xs) :
    value ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    simp only [List.foldr_cons]
    rcases member with rfl | tail
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)

theorem Tree.child_height_lt (size work : Nat) (children : List Tree) (child : Tree)
    (member : child ∈ children) : child.height < (Tree.node size work children).height := by
  have bound := le_foldr_max (children.map Tree.height) child.height (List.mem_map.mpr ⟨child, member, rfl⟩)
  simp only [Tree.height]
  omega



/-- Summing a sufficient number of complete levels gives the total work. -/
theorem Tree.sum_levels (tree : Tree) (levels : Nat) (complete : tree.height ≤ levels) :
    sumBelow levels tree.levelCost = tree.totalCost := by
  induction tree using Tree.totalCost.induct generalizing levels with
  | case1 size work children ih =>
    cases levels with
    | zero => simp only [Tree.height] at complete; omega
    | succ levels =>
      rw [sumBelow_shift]
      simp only [Tree.levelCost, Tree.totalCost, sumBelow_map_sum]
      congr 1
      congr 1
      apply List.map_congr_left
      intro child member
      exact ih child member levels (by have := Tree.child_height_lt size work children child member; omega)

/-- The exact recursion-tree decomposition by levels. -/
theorem Tree.total_eq_levels (tree : Tree) :
    tree.totalCost = sumBelow tree.height tree.levelCost :=
  (tree.sum_levels tree.height (Nat.le_refl _)).symm














/-- Every consistent finite tree computes the cost specified by the recurrence.
Different shapes at different input sizes and unequal subtree heights are allowed. -/
theorem consistent_total (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (cost : Nat → Nat) (baseCost : ∀ n, n < cutoff → cost n = base n)
    (recurrence : Chapter4Substitution.ExactRecurrence children toll cutoff cost)
    (tree : Tree) (consistent : Consistent children toll base cutoff tree) :
    tree.totalCost = cost tree.rootSize := by
  induction tree using Tree.totalCost.induct with
  | case1 size work forest ih =>
    cases consistent with
    | leaf size small =>
      simpa [Tree.totalCost, Tree.rootSize] using (baseCost size small).symm
    | branch size forest large sizes subtrees =>
      simp only [Tree.totalCost, Tree.rootSize]
      rw [recurrence size large, ← sizes]
      simp only [Chapter4Substitution.childSum, List.map_map]
      congr 1
      congr 1
      apply List.map_congr_left
      intro tree member
      exact ih tree member (subtrees tree member)

/-- Assemble a forest while retaining the exact ordered list of root sizes. -/
theorem forest_exists (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (sizes : List Nat)
    (available : ∀ n ∈ sizes, ∃ tree, tree.rootSize = n ∧ Consistent children toll base cutoff tree) :
    ∃ forest : List Tree, forest.map Tree.rootSize = sizes ∧
      ∀ tree ∈ forest, Consistent children toll base cutoff tree := by
  induction sizes with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons size sizes ih =>
    obtain ⟨head, headSize, headProof⟩ := available size (by simp)
    obtain ⟨tail, tailSizes, tailProof⟩ := ih (fun n member => available n (by simp [member]))
    refine ⟨head::tail, ?_, ?_⟩
    · simp [headSize, tailSizes]
    · intro tree member
      rcases List.mem_cons.mp member with rfl | later
      · exact headProof
      · exact tailProof tree later

/-- Strictly decreasing natural child sizes guarantee a finite recursion tree
for every input size, even with size-dependent arity and unequal splits. -/
theorem consistent_exists (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (smaller : Chapter4Substitution.SmallerChildren children cutoff) (size : Nat) :
    ∃ tree, tree.rootSize = size ∧ Consistent children toll base cutoff tree := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    by_cases small : size < cutoff
    · exact ⟨.node size (base size) [], rfl, .leaf size small⟩
    · have large : cutoff ≤ size := by omega
      obtain ⟨forest, sizes, subtrees⟩ := forest_exists children toll base cutoff (children size)
        (fun child member => ih child (smaller size large child member))
      exact ⟨.node size (toll size) forest, rfl, .branch size forest large sizes subtrees⟩

























end Chapter4RecursionTree

end CLRS
end

namespace CLRS
end CLRS
open CLRS
namespace CLRS.Chapter4RecursionTree
end CLRS.Chapter4RecursionTree
open CLRS.Chapter4RecursionTree

theorem solution (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (cost : Nat → Nat) (smaller : Chapter4Substitution.SmallerChildren children cutoff)
    (baseCost : ∀ n, n < cutoff → cost n = base n)
    (recurrence : Chapter4Substitution.ExactRecurrence children toll cutoff cost) (size : Nat) :
    ∃ tree, tree.rootSize = size ∧ Consistent children toll base cutoff tree ∧
      cost size = tree.totalCost ∧ cost size = sumBelow tree.height tree.levelCost := by
  obtain ⟨tree, root, consistent⟩ := consistent_exists children toll base cutoff smaller size
  have exactCost := consistent_total children toll base cutoff cost baseCost recurrence tree consistent
  rw [root] at exactCost
  exact ⟨tree, root, consistent, exactCost.symm, exactCost.symm.trans tree.total_eq_levels⟩
