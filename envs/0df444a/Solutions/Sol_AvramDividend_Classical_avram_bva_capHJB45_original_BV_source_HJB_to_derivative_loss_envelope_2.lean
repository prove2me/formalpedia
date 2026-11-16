-- Prove2me | solution 2 for AvramDividend.Classical.avram_bva_capHJB45_original_BV_source_HJB_to_derivative_loss_envelope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:39:50.18467+00:00
-- url     : https://prove2.me/submissions/51f8705e-338a-4435-ad7b-1bce06b4c541
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB45_left_endpoint_BV_derivative_loss_envelope
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
      ∀ y ∈ Icc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      X.drift * deriv w y ≤ (W + A) + η * M := by
  intro b hb y hy M hM
  by_cases hye : y = ε
  · subst y
    exact avram_bva_capHJB45_left_endpoint_BV_derivative_loss_envelope
      X hBV q w ε c W η A hε hεc hwGen hwUpper hLoss b hb M hM
  · have hypos : ε < y := lt_of_le_of_ne hy.1 (Ne.symm hye)
    have hyc : y < c := lt_of_le_of_lt hy.2 hb.2
    have hyInterior : y ∈ Ioo ε c := ⟨hypos, hyc⟩
    have hGI := (hwGen y hyInterior).1
    have hGenerator := (hwGen y hyInterior).2
    have hW := hwUpper y hyInterior
    have hJump := hLoss b hb y hy M hM
    have hFormula := boundedVariation_generator_physical_drift_representation
      X hBV w y hGI
    linarith
