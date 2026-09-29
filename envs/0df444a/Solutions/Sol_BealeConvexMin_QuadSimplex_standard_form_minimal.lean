-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.standard_form_minimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:45:50.906985+00:00
-- url     : https://prove2.me/submissions/f5632da7-5eac-47bc-9a5b-26a54f294717

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau

namespace BealeConvexMin.QuadSimplex

theorem aux_sfm_lin {n N : ℕ} (T : Tableau n N) (hstd : IsStandardForm T)
    (z : Fin (N + 1) → ℝ)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → z k.succ = 0) (i : Fin N) :
    T.c i.succ 0 * z i.succ = 0 := by
  by_cases h : T.lab i = none
  · rw [hstd i h, zero_mul]
  · rw [hzres i h, mul_zero]

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem solution {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hpsd : (T.c.submatrix Fin.succ Fin.succ).PosSemidef) (hstd : IsStandardForm T)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → z k.succ = 0) :
    T.c 0 0 ≤ quadValue T.c z := by
  have hq := hpsd.dotProduct_mulVec_nonneg (fun i => z i.succ)
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.submatrix_apply] at hq
  have hsym : ∀ i j, T.c i j = T.c j i := fun i j => by
    have := congrFun (congrFun hsymm j) i
    simpa [Matrix.transpose_apply] using this
  have h1 : ∀ i : Fin N, T.c 0 i.succ * z i.succ = 0 := fun i => by
    rw [hsym]; exact aux_sfm_lin T hstd z hzres i
  have h2 : ∀ i : Fin N, T.c i.succ 0 * z i.succ = 0 := fun i =>
    aux_sfm_lin T hstd z hzres i
  unfold quadValue
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ (f := fun l => T.c _ l * z _ * z l), hz0, mul_one, h1, h2,
    Finset.sum_const_zero, add_zero, zero_add]
  have : ∑ i : Fin N, z i.succ * ∑ j : Fin N, T.c i.succ j.succ * z j.succ
      = ∑ i : Fin N, ∑ j : Fin N, T.c i.succ j.succ * z i.succ * z j.succ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  linarith
