-- Prove2me | solution 1 for AvramDividend.Classical.bv_zero_surviving_weighted_stieltjes_prefix_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T16:24:09.261537+00:00
-- url     : https://prove2.me/submissions/134bf036-8d09-42af-88aa-75b37b65e1a2

import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_zero_deficit_weighted_stieltjes_prefix_ae
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- On almost every strictly surviving zero-barrier path, the actual
running-supremum Stieltjes dividend measure equals drift-volume to T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < barrierRuinTime X 0 ω →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂(dividendMeasure (runningSup X) ω)) =
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let D : Ω → ℝ := fun ω => X.drift * (T : ℝ) - X.X T ω
  have hPosReal : P.real {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧ 0 < D ω} = 0 := by
    simpa only [D] using
      bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
        X hBV hFinite T
  have hPosNull : P {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧ 0 < D ω} = 0 :=
    (measureReal_eq_zero_iff).mp hPosReal
  have hAE : ∀ᵐ ω ∂P,
      ¬ ((T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧ 0 < D ω) := by
    apply ae_iff.mpr
    simpa only [not_not] using hPosNull
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω := by
    filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV T] with ω hx
    dsimp [D]
    linarith
  filter_upwards
    [hAE, hNonneg, bv_zero_deficit_weighted_stieltjes_prefix_ae
      X hStanding hBV] with ω hNoPos hD0 hSt
  intro hSurv f
  have hNotPos : ¬ 0 < D ω := by
    intro hPos
    exact hNoPos ⟨hSurv, hPos⟩
  have hZero : D ω = 0 := le_antisymm (le_of_not_gt hNotPos) hD0
  exact hSt T (by simpa only [D] using hZero) f
