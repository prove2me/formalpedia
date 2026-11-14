-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB45s_original_BV_strict_source_HJB_to_derivative_loss_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T17:15:29.821204+00:00
-- url     : https://prove2.me/submissions/5db45a5b-1f51-46f8-b68d-e49e9586291d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Original spectrally negative bounded variation source, physical finite cap, capHJB45. -/
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
      ∀ y ∈ Ioc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
        A + η * M) :
    ∀ b ∈ Ioo ε c,
      ∀ y ∈ Ioc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      X.drift * deriv w y ≤ (W + A) + η * M := by
  intro b hb y hy M hM
  have hyOpen : y ∈ Ioo ε c :=
    ⟨hy.1, lt_of_le_of_lt hy.2 hb.2⟩
  have hGenI := (hwGen y hyOpen).1
  have hGenSign := (hwGen y hyOpen).2
  rw [boundedVariation_generator_physical_drift_representation
    X hBV w y hGenI] at hGenSign
  have hQ := hwUpper y hyOpen
  have hB := hLoss b hb y hy M hM
  linarith
