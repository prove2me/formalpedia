-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_uniform_BV_full_HJB_and_strict_cash_failure_same_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:11:33.828577+00:00
-- url     : https://prove2.me/submissions/b102513f-2656-41b5-800e-e69a72ad5e53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
import Theorems.Thm_AvramDividend_Classical_avram_b29_original_positive_probability_drift_source_failure
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
      (let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let D := barrierStrategy X 0 0
       (∀ y : ℝ, 0 < y → ENNReal.ofReal y < (1 : ℝ≥0∞) →
          X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
       IsAdmissibleLe X 0 (1 : ℝ≥0∞) D) ∧
      0 < P {ω |
        let D := barrierStrategy X 0 0
        let T : ℝ := 1 / 10
        let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
        let u : ℕ → ℕ → ℝ≥0 := fun n i =>
          ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
        let F : ℕ → ℝ := fun n =>
          (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
              Iio (T - T / ((n : ℝ) + 2)),
            ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
            (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
              Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
             else 0)
        let L : ℕ → ℝ := fun n =>
          let Z : ℕ → ℝ := fun i => Function.leftLim
            (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
          ∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
              Real.exp (-(u n i : ℝ)) *
                (X.drift * deriv w (Z i) - w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
        ¬ Tendsto (fun n => max (F n - (w 0 + L n)) 0)
          atTop (𝓝 (0 : ℝ))} := by
  obtain ⟨P, 𝓕, X, hStanding, hBV, hν, hActivity, hDrift,
    hSigma, hPositive, hAnal⟩ :=
      avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
  dsimp at hAnal
  rcases hAnal with ⟨hCont, h0, hNeg, hSmooth, hGen, hGrad,
    hAdm, hNonneg, hJump⟩
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧
    (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift)}
  have hPath : ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift := by
    intro ω hω t ht
    exact hω.2 t ht
  have hBad :=
    avram_b29_original_positive_probability_drift_source_failure
      X E hPositive hDrift hPath
  refine ⟨P, 𝓕, X, hStanding, hBV, hDrift, ?_, hBad⟩
  dsimp
  exact ⟨hGen, hAdm⟩
