-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:33:24.470379+00:00
-- url     : https://prove2.me/submissions/7ff0a3db-abfc-4432-8dd0-2fd9503f430e

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

theorem aux_optcrit_lin {n N : ℕ} (T : Tableau n N)
    (hopt : ∀ k : Fin N, ¬ IsProfitable T k)
    (z : Fin (N + 1) → ℝ)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → 0 ≤ z k.succ) (k : Fin N) :
    0 ≤ T.c k.succ 0 * z k.succ := by
  have h := hopt k
  unfold IsProfitable at h
  push Not at h
  by_cases hl : T.lab k = none
  · have := h.1 hl
    rw [this, zero_mul]
  · exact mul_nonneg (h.2 hl) (hzres k hl)

theorem aux_optcrit_quad {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hpsd : (c.submatrix Fin.succ Fin.succ).PosSemidef) (z : Fin (N + 1) → ℝ) :
    0 ≤ ∑ k : Fin N, ∑ l : Fin N, c k.succ l.succ * z k.succ * z l.succ := by
  have h := hpsd.dotProduct_mulVec_nonneg (fun k => z k.succ)
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, star_trivial,
    Finset.mul_sum] at h
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_)
  ring

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem solution {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hpsd : (T.c.submatrix Fin.succ Fin.succ).PosSemidef)
    (hopt : ∀ k : Fin N, ¬ IsProfitable T k)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → 0 ≤ z k.succ)
    (hrow : ∀ j : Fin n, 0 ≤ ∑ l, T.row j l * z l) :
    T.c 0 0 ≤ quadValue T.c z := by
  have hq := aux_optcrit_quad T.c hpsd z
  have hl : 0 ≤ ∑ k : Fin N, T.c k.succ 0 * z k.succ :=
    Finset.sum_nonneg fun k _ => aux_optcrit_lin T hopt z hzres k
  have hs : ∀ l : Fin N, T.c 0 l.succ = T.c l.succ 0 := fun l => hsymm.apply l.succ 0
  unfold quadValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ (fun l => T.c _ l * _ * z l), hz0, hs, Finset.sum_add_distrib]
  simp only [mul_one]
  linarith
