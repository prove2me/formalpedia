-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_strict_survival_null_of_mesh_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:29:09.945252+00:00
-- url     : https://prove2.me/submissions/6f756551-7f15-436a-b4dd-1fa4fdfe0968

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_inverse_frequency_mesh_gap_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_mesh_exponential_gap_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_vanishing_expected_deficit_bound_forces_null_event
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The actual BV infinite-activity zero barrier has null strict survival under uniform mesh bounds. -/
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
  letI : IsProbabilityMeasure P := X.isProbability
  have hNonneg :
      ∀ᵐ ω ∂P, 0 ≤ (T : ℝ) * X.drift - X.X T ω := by
    filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV T]
      with ω hω
    exact sub_nonneg.mpr hω
  have hAtom :
      P {ω : Ω | (T : ℝ) * X.drift - X.X T ω = 0} = 0 :=
    (measureReal_eq_zero_iff).mp
      (bv_infinite_activity_drift_deficit_zero_atom X hBV hνinf T hT)
  have hGap :=
    bv_inverse_frequency_mesh_gap_tendsto_zero
      X hBV δ θ c hθ hθne hProduct
  have hVanishing :=
    mesh_exponential_gap_tendsto_zero
      (fun n => δ n * (X.drift * θ n - X.ψ (θ n))) C hGap
  exact vanishing_expected_deficit_bound_forces_null_event
    P {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}
    (fun ω => (T : ℝ) * X.drift - X.X T ω)
    hNonneg hAtom hInt
    (fun n => C * (1 - Real.exp (-(δ n * (X.drift * θ n - X.ψ (θ n))))))
    hVanishing hBound
