-- Prove2me | solution 2 for AvramDividend.Classical.bv_infinite_activity_strict_survival_null_of_mesh_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:30:27.716967+00:00
-- url     : https://prove2.me/submissions/a7e64e41-8eca-411b-becc-07bfb01ce18f

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_inverse_frequency_mesh_gap_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_mesh_exponential_gap_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_vanishing_expected_deficit_bound_forces_null_event
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Measure.Real

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (δ θ : ℕ → ℝ) (c C : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθne : ∀ n, θ n ≠ 0)
    (hProduct : ∀ n, δ n * θ n = c)
    (hInt : Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω)) P)
    (hBound : ∀ n : ℕ,
      (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω) ω ∂P) ≤
      C * (1 - Real.exp (-(δ n * (X.drift * θ n - X.ψ (θ n)))))) :
    P {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω} = 0 := by
  haveI := X.isProbability
  refine vanishing_expected_deficit_bound_forces_null_event P _ (fun ω => (T : ℝ) * X.drift - X.X T ω) ?_ ?_ hInt _ ?_ hBound
  · filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV T] with ω hω
    linarith
  · have h := bv_infinite_activity_drift_deficit_zero_atom X hBV hνinf T hT
    rwa [measureReal_eq_zero_iff] at h
  · exact mesh_exponential_gap_tendsto_zero _ C
      (bv_inverse_frequency_mesh_gap_tendsto_zero X hBV δ θ c hθ hθne hProduct)
