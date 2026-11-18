-- Prove2me | solution 1 for EditGV897.Main.witness_count_correct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:26:32.701936+00:00
-- url     : https://prove2.me/submissions/519e98b1-de4b-4178-9f7a-1815f7d1b34c

import Definitions.Def_EditGV897_Main_Codec

import Theorems.Thm_EditGV897_Main_affine_count_correct

namespace EditGV897.Main
private theorem affineCount_correct {n : ℕ} (E : List (Equation n)) :
  affineCount E = (affineSet E).card := affine_count_correct n E
end EditGV897.Main


namespace EditGV897.Main

 theorem difference_apply {n : ℕ} (f : Affine n) (x : Word n) :
    (difference f).apply x = differenceAt f x := by
  classical
  funext i
  simp only [Affine.apply, difference, differenceAt, Pi.add_apply]
  unfold dot
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp [add_assoc]

 theorem pullZero_spec {n : ℕ} (d : Affine n) (h x : Word n) :
    equationHolds (pullZero d h) x ↔ dot h (d.apply x) = 0 := by
  have he : dot (fun j => ∑ i, h i * d.matrix i j) x =
      ∑ i, h i * dot (d.matrix i) x := by
    simp only [dot, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  unfold equationHolds pullZero
  simp only
  rw [he]
  have he' : dot h (d.apply x) = (∑ i, h i * dot (d.matrix i) x) + dot h d.offset := by
    simp [dot, Affine.apply, mul_add, Finset.sum_add_distrib]
  rw [he', CharTwo.add_eq_zero]

 theorem fixedEquations_spec {n : ℕ} (f : Affine n) (x : Word n) :
    (∀ e ∈ fixedEquations f, equationHolds e x) ↔ differenceAt f x = 0 := by
  rw [← difference_apply]
  constructor
  · intro h
    funext i
    have hi := h ((difference f).matrix i, f.offset i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    change dot ((difference f).matrix i) x + f.offset i = 0
    exact CharTwo.add_eq_zero.mpr hi
  · intro h e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    have hi := congrFun h i
    change dot ((difference f).matrix i) x + f.offset i = 0 at hi
    exact CharTwo.add_eq_zero.mp hi

 theorem collisionEquations_spec {n : ℕ} (f : Affine n) (G : Rows n) (x : Word n) :
    (∀ e ∈ collisionEquations f G, equationHolds e x) ↔
      syndrome G (differenceAt f x) = G.map (fun _ => 0) := by
  simp only [collisionEquations, List.forall_mem_map, pullZero_spec, difference_apply,
    syndrome, List.map_eq_map_iff]

private theorem list_witness_double_count {n : ℕ} (F : Family n) (G : Rows n) (S : Finset (Word n)) :
    (F.map (fun f => (S.filter (fun x => decide
      (differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0)))).card)).sum =
      witnessSum F G S := by
  classical
  induction F with
  | nil => simp [witnessSum, witnessesAt]
  | cons f F ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    have hpoint (x : Word n) : witnessesAt (f :: F) G x =
        (if differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0)
        then 1 else 0) + witnessesAt F G x := by
      unfold witnessesAt
      by_cases hw : differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0)
      · simp only [List.filter_cons, decide_eq_true hw, if_pos hw, ite_true, List.length_cons]
        omega
      · simp only [List.filter_cons, decide_eq_false hw, if_neg hw, Bool.false_eq_true, ite_false, zero_add]
    unfold witnessSum
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp only [Finset.card_filter, decide_eq_true_eq]

 theorem witnessCount_correct {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E = witnessSum F G (affineSet E) := by
  classical
  unfold witnessCount
  simp_rw [affineCount_correct]
  have heach (f : Affine n) :
      (affineSet (E ++ collisionEquations f G)).card - (affineSet (E ++ fixedEquations f)).card =
      ((affineSet E).filter (fun x => decide (differenceAt f x ≠ 0 ∧
        syndrome G (differenceAt f x) = G.map (fun _ => 0)))).card := by
    have hsub : affineSet (E ++ fixedEquations f) ⊆ affineSet (E ++ collisionEquations f G) := by
      intro x hx
      simp only [affineSet, Finset.mem_filter, Finset.mem_univ, true_and,
        List.forall_mem_append, fixedEquations_spec, collisionEquations_spec] at hx ⊢
      refine ⟨hx.1, ?_⟩
      simp [hx.2, syndrome, dot]
    have hdiff : affineSet (E ++ collisionEquations f G) \ affineSet (E ++ fixedEquations f) =
        (affineSet E).filter (fun x => decide (differenceAt f x ≠ 0 ∧
          syndrome G (differenceAt f x) = G.map (fun _ => 0))) := by
      ext x
      simp only [affineSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        List.forall_mem_append, fixedEquations_spec, collisionEquations_spec, decide_eq_true_eq]
      tauto
    rw [← Finset.card_sdiff_of_subset hsub, hdiff]
  simp_rw [heach]
  exact list_witness_double_count F G (affineSet E)

end EditGV897.Main

open EditGV897.Main

theorem solution (n : ℕ) (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E = witnessSum F G (affineSet E) := witnessCount_correct F G E