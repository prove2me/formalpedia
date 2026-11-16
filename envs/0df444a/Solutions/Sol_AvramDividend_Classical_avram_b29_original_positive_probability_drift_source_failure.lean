-- Prove2me | solution 1 for AvramDividend.Classical.avram_b29_original_positive_probability_drift_source_failure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:15:30.376019+00:00
-- url     : https://prove2.me/submissions/b32d2725-191a-4a8b-9009-1f1900e90c77

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (E : Set Ω) (hE : 0 < P E)
    (hDrift : X.drift = 1)
    (hPath : ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift) :
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
  apply lt_of_lt_of_le hE
  apply measure_mono
  intro ω hω
  exact
    avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
      X ω hDrift (hPath ω hω)
