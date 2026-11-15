-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB45_interior_BV_source_HJB_to_derivative_loss_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:14:43.40329+00:00
-- url     : https://prove2.me/submissions/550839a1-ab50-4147-810d-ef978c1cc68d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (ε c W η A : ℝ)
    (hε : 0 < ε) (hεc : ε < c)
    (hwGen : ∀ y ∈ Ioo ε c,
      X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0)
    (hwUpper : ∀ y ∈ Ioo ε c, q * w y ≤ W)
    (hLoss : ∀ b ∈ Ioo ε c,
      ∀ y ∈ Icc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
        A + η * M) :
    ∀ b ∈ Ioo ε c,
      ∀ y ∈ Ioo ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      X.drift * deriv w y ≤ (W + A) + η * M := by
  intro b hb y hy M hM
  have hyc : y ∈ Ioo ε c := ⟨hy.1, lt_trans hy.2 hb.2⟩
  obtain ⟨hInt, hGen⟩ := hwGen y hyc
  have hRep :=
    boundedVariation_generator_physical_drift_representation X hBV w y hInt
  have hUpper := hwUpper y hyc
  have hClosed : y ∈ Icc ε b := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hLossBound := hLoss b hb y hClosed M hM
  rw [hRep] at hGen
  linarith
