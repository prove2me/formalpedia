-- Prove2me | solution 1 for AvramDividend.Classical.cstar_optimal_barrier_of_regular_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:57:34.146808+00:00
-- url     : https://prove2.me/submissions/c42d7d08-858a-4467-95bf-b53897af6bb2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_shape
import Theorems.Thm_AvramDividend_Classical_scale_secant_of_derivative_lower_bound

open AvramDividend.Classical
open scoped ENNReal

theorem solution
    (W : ℝ → ℝ) (hfinite : cstar W < ⊤)
    (hW : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hshape : ((cstar W).toReal = 0 ∧ W 0 = 0) ∨
      ∃ d : ℝ, 0 < d ∧
        scaleDeriv W (cstar W).toReal = (d : EReal) ∧
        (∀ a : ℝ, 0 ≤ a →
          scaleDeriv W a = ⊤ ∨
            (scaleDeriv W a).toReal = 0 ∨
            d ≤ (scaleDeriv W a).toReal) ∧
        ContinuousOn W (Set.Icc 0 (cstar W).toReal) ∧
        DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal) ∧
        (∀ t ∈ Set.Ioo 0 (cstar W).toReal, d ≤ deriv W t)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  apply cstar_optimal_barrier_of_shape W hfinite hW
  rcases hshape with hzero | ⟨d, hd, hc, hden, hcont, hdiff, hder⟩
  · exact Or.inl hzero
  · right
    refine ⟨d, hd, hc, hden, ?_⟩
    exact scale_secant_of_derivative_lower_bound
      W (cstar W).toReal d hcont hdiff hder
