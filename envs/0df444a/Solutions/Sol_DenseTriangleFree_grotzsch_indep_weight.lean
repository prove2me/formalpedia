-- Prove2me | solution 1 for DenseTriangleFree.grotzsch_indep_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:07.442579+00:00
-- url     : https://prove2.me/submissions/8077854d-644a-49a5-8038-2e0c2e2d9f80

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Theorems.Thm_DenseTriangleFree_grotzsch_indep_aux

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution (s : Fin 11 → Prop) [DecidablePred s]
    (hs : ∀ i j, grotzsch.Adj i j → s i → s j → False) :
    ∑ i, (if s i then grotzschWt i else 0) ≤ 10 := by
  have hb : ∀ b : Fin 11 → Bool, grotzschIndepB b = true → grotzschWtB b ≤ 10 := by
    intro b hb
    have := grotzsch_indep_aux (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10)
    have e : ![b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7, b 8, b 9, b 10] = b := by
      funext i; fin_cases i <;> rfl
    rw [e] at this
    exact this hb
  have h1 := hb (fun i => decide (s i)) (by
    simp only [grotzschIndepB, List.all_eq_true, List.mem_finRange, true_implies]
    intro i j
    by_cases h : grotzschAdjB i j = true
    · by_cases hi : s i
      · by_cases hj : s j
        · exact (hs i j h hi hj).elim
        · simp [hj]
      · simp [hi]
    · simp [h])
  have e : grotzschWtB (fun i => decide (s i)) = ∑ i, (if s i then grotzschWt i else 0) := by
    simp only [grotzschWtB, decide_eq_true_eq]
    rw [← Fin.sum_univ_def]
  omega
end DenseTriangleFree
