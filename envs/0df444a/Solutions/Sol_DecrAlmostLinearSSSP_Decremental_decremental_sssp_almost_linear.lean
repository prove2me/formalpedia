-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.decremental_sssp_almost_linear
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:47:54.086443+00:00
-- url     : https://prove2.me/submissions/13daa4ff-2610-4f51-b2b6-f9aafae9803c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_polynomial_weight_sssp
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_general_domain_adapter

set_option autoImplicit false
open scoped ENNReal NNReal
open DecrAlmostLinearSSSP.Decremental

theorem solution :
    ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ),
      0 < C ∧ 0 < queryBound ∧ Subpolynomial a ∧
      ∀ i : Input, i.Valid → Maintains p C a queryBound true i := by
  obtain ⟨p, C, a, queryBound, hC, hquery, ha, hpoly, _⟩ := polynomial_weight_sssp 2
  exact general_domain_adapter p C a queryBound hC hquery ha hpoly
