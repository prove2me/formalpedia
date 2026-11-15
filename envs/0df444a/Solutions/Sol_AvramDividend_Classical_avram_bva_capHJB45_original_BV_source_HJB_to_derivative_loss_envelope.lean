-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB45_original_BV_source_HJB_to_derivative_loss_envelope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:22:20.173235+00:00
-- url     : https://prove2.me/submissions/ad1c8a7c-e02c-46c2-b16f-a3e5ce0c9e3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB45s_original_BV_strict_source_HJB_to_derivative_loss_envelope
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
  have hLossStrict : ∀ b ∈ Ioo ε c,
      ∀ y ∈ Ioc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
        A + η * M := by
    intro b hb y hy M hM
    exact hLoss b hb y ⟨le_of_lt hy.1, hy.2⟩ M hM
  intro b hb y hy M hM
  by_cases he : y = ε
  · subst y
    exact AvramDividend.Classical.avram_bva_capHJB45_left_endpoint_BV_derivative_loss_envelope
      X hBV q w ε c W η A hε hεc hwGen hwUpper hLoss b hb M hM
  · have hgt : ε < y := lt_of_le_of_ne hy.1 (Ne.symm he)
    exact AvramDividend.Classical.avram_bva_capHJB45s_original_BV_strict_source_HJB_to_derivative_loss_envelope
      X hBV q w ε c W η A hε hεc hwGen hwUpper hLossStrict
      b hb y ⟨hgt, hy.2⟩ M hM
