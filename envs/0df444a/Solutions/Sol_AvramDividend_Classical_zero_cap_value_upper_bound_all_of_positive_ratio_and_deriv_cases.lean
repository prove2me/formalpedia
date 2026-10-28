-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound_all_of_positive_ratio_and_deriv_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:41:07.077111+00:00
-- url     : https://prove2.me/submissions/736da0e3-3667-4589-90a8-712aa5e0cba8

import Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The proved zero-reserve boundary estimate extends to arbitrary initial
capital under the same explicit positive-barrier and derivative hypotheses. -/
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
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  obtain ⟨hval, hbound⟩ :=
    zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
      X hX q hq W hW hscale hcont hderiv
  intro x hx
  exact zero_cap_value_upper_bound_of_zero_bound X q W hbound hval x hx
