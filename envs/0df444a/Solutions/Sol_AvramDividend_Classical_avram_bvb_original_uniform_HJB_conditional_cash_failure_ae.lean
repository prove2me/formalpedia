-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_uniform_HJB_conditional_cash_failure_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:20:36.652065+00:00
-- url     : https://prove2.me/submissions/bd4f997e-765a-4259-aae5-a580646b0329

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧ X.drift = 1 ∧
      (let D := barrierStrategy X 0 0
       let T : ℝ := 1 / 10
       let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let u : ℕ → ℕ → ℝ≥0 := fun n i =>
         ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
       let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
         (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
             Iio (T - T / ((n : ℝ) + 2)),
           ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
           (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
             Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
            else 0)
       let L : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
         let Z : ℕ → ℝ := fun i => Function.leftLim
           (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
         ∑ i ∈ Finset.range (n + 1),
           if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
             Real.exp (-(u n i : ℝ)) *
               (X.drift * deriv w (Z i) - w (Z i)) *
               ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
       IsAdmissibleLe X 0 (1 : ℝ≥0∞) D ∧
       (∀ y : ℝ, 0 < y → ENNReal.ofReal y < (1 : ℝ≥0∞) →
         X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
       ¬ (∀ᵐ ω ∂P,
         (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift) →
         Tendsto (fun n => max (F n ω - (w 0 + L n ω)) 0) atTop (𝓝 (0 : ℝ)))) := by
  rcases avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
    with ⟨P, 𝓕, X, hStanding, hBV, hν, hFinite, hDrift, hσ, hEvent, hProperties⟩
  dsimp at hProperties
  rcases hProperties with
    ⟨hwCont, hw0, hwNeg, hwSmooth, hwGen, hwGrad, hD, hwNonneg, hjump⟩
  refine ⟨P, 𝓕, X, hStanding, hBV, hDrift, hD, hwGen, ?_⟩
  have hPos : 0 < P {ω | ∀ t : ℝ≥0, t ≤ 1 →
      X.X t ω = (t : ℝ) * X.drift} := by
    apply lt_of_lt_of_le hEvent
    apply measure_mono
    intro ω hω
    exact hω.2
  intro hAE
  have hBad : ∀ᵐ ω ∂P,
      ω ∉ {ω | ∀ t : ℝ≥0, t ≤ 1 →
        X.X t ω = (t : ℝ) * X.drift} := by
    filter_upwards [hAE] with ω hω
    intro hPath
    have hFail :=
      avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
        X ω hDrift hPath
    exact hFail (hω hPath)
  have hz : P {ω | ∀ t : ℝ≥0, t ≤ 1 →
      X.X t ω = (t : ℝ) * X.drift} = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr hBad
  exact (ne_of_gt hPos) hz
