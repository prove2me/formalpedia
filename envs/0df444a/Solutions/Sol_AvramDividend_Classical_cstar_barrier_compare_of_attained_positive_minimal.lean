-- Prove2me | solution 1 for AvramDividend.Classical.cstar_barrier_compare_of_attained_positive_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T13:41:57.505779+00:00
-- url     : https://prove2.me/submissions/98ea788f-4af6-4677-b11c-29dc7687923e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_minimizer
import Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_regular_minimal

open AvramDividend.Classical
open scoped ENNReal

theorem solution
    (W : ℝ → ℝ)
    (hW : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hattain : (cstar W).toReal ∈ cstarSet W)
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hboundary : scaleDeriv W 0 = ⊤ ∨
      (scaleDeriv W 0).toReal = 0 ∨
      deriv W (cstar W).toReal ≤ (scaleDeriv W 0).toReal)
    (hcont : ContinuousOn W (Set.Icc 0 (cstar W).toReal))
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  have hfinite : cstar W < ⊤ :=
    cstar_lt_top_of_minimizer W ⟨(cstar W).toReal, hattain⟩
  have hpos : 0 < (cstar W).toReal := hattain.1
  have hmin : ∀ a : ℝ, 0 < a →
      deriv W (cstar W).toReal ≤ deriv W a := hattain.2
  have hscale :
      scaleDeriv W (cstar W).toReal =
        ((deriv W (cstar W).toReal : ℝ) : EReal) := by
    simp [scaleDeriv, ne_of_gt hpos]
  have hden : ∀ a : ℝ, 0 ≤ a →
      scaleDeriv W a = ⊤ ∨ (scaleDeriv W a).toReal = 0 ∨
        deriv W (cstar W).toReal ≤ (scaleDeriv W a).toReal := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      exact hboundary
    · right
      right
      have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      simpa [scaleDeriv, ha0] using hmin a hapos
  apply cstar_optimal_barrier_of_regular_minimal W hfinite hW
  right
  refine ⟨deriv W (cstar W).toReal, hpositive, hscale,
    hden, hcont, hdiff, ?_⟩
  intro t ht
  exact hmin t ht.1
