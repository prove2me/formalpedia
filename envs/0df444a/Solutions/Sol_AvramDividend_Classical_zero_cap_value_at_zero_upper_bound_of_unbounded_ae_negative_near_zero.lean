-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_unbounded_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:52:47.46352+00:00
-- url     : https://prove2.me/submissions/1f411b10-3e69-468d-bd47-47b69cc53aec

import Theorems.Thm_AvramDividend_Classical_local_verification_per_strategy_to_capped_value_bound
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- In the regular unbounded-variation branch, reflection dominates every zero-capped strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  apply local_verification_per_strategy_to_capped_value_bound
    X q 0 0 (barrierValue W 0)
  intro D hD
  calc
    dividendValue X q 0 D ≤
        dividendValue X q 0 (barrierStrategy X 0 0) :=
      zero_cap_admissible_dividendValue_le_barrier_at_zero X hX q hq D hD
    _ = ENNReal.ofReal (barrierValue W 0 0) :=
      (barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
        X hX q hq W hW hnbv hNear).2
