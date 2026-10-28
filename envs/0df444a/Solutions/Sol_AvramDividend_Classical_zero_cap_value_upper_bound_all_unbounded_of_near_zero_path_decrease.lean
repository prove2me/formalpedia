-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_near_zero_path_decrease
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:36:36.504736+00:00
-- url     : https://prove2.me/submissions/5cdd3cd9-a167-481d-9e77-e3abb2bb9821

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_path_decrease
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_unbounded_of_instant_ruin
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Arbitrarily early strict path decreases are sufficient for the global
zero-cap verification inequality in the unbounded-variation regime. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hDecrease : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s t : ℝ≥0, s ≤ t ∧ t < ε ∧ X.X t ω < X.X s ω) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  have hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 :=
    hDecrease.mono (fun ω hω =>
      barrierRuinTime_zero_of_near_zero_path_decrease X ω hω)
  exact zero_cap_value_upper_bound_all_unbounded_of_instant_ruin
    X hX q hq W hW hnbv hRuin
