-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:27:41.910114+00:00
-- url     : https://prove2.me/submissions/154c190d-5f1e-4c98-86b3-da1714dde992

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_ratio_and_finite_deriv_limit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_ratio_and_divergent_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The original zero-cap package follows from verified positive-barrier
valuation and one of the two right-derivative limit alternatives. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv :
      (∃ d : ℝ, d ≠ 0 ∧ Tendsto (fun y : ℝ => deriv W y)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds d)) ∨
      Tendsto (fun y : ℝ => deriv W y)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    0 ≤ barrierValue W 0 0 ∧
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  constructor
  · exact barrierValue_zero_boundary_nonneg X hX q hq W hW
  · apply zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W
    rcases hderiv with ⟨d, hd, hfinite⟩ | hinfinite
    · exact barrierStrategy_zero_boundary_of_positive_ratio_and_finite_deriv_limit
        X q W hscale hcont d hd hfinite
    · exact barrierStrategy_zero_boundary_of_positive_ratio_and_divergent_deriv
        X q W hscale hcont hinfinite
