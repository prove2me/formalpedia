-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_survivor_terminal_positive_omission_integrable_from_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:02:34.535339+00:00
-- url     : https://prove2.me/submissions/1dc191c6-da9c-43c5-8abb-83f983310036

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_strict_survivor_true_terminal_positive_omission_uniform_L1_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (x + X.X t ω - rightLimit D t ω))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, AEStronglyMeasurable (Err m) P) →
    ∀ m, Integrable (Err m) P := by
  intro S Err hErrMeas
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨K, hK, hBound⟩ :=
    avram_bva_a22_original_strict_survivor_true_terminal_positive_omission_uniform_L1_envelope
      X hX hBV q hq w hw_cont x D hD hw_nonneg T hT u huniform
  intro m
  have hPos (ω : Ω) : 0 ≤ Err m ω := by
    dsimp [Err]
    split_ifs <;> positivity
  have hNorm : ∀ᵐ ω ∂P, ‖Err m ω‖ ≤ K := by
    filter_upwards [hBound m] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hPos ω)] using hω
  exact Integrable.of_bound (hErrMeas m) K hNorm
