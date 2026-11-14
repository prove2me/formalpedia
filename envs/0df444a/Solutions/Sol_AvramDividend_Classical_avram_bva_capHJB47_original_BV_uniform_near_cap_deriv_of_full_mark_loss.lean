-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB47_original_BV_uniform_near_cap_deriv_of_full_mark_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T18:25:39.705519+00:00
-- url     : https://prove2.me/submissions/47f20abf-8ea7-44a5-8a7e-aefe7a968458

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB44s_original_BV_derivative_maximum_from_strict_HJB_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB45s_original_BV_strict_source_HJB_to_derivative_loss_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- HJB47 original source bridge: HJB44s and HJB45s both independently Proved; source retains original closed loss input, restricts solely for strict generator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (ε c W A η B : ℝ)
    (hε : 0 < ε) (hεc : ε < c)
    (hη : η < X.drift)
    (hLocal : ∀ t ∈ Icc (ε / 2) ε, deriv w t ≤ B)
    (hMax : ∀ b ∈ Ioo ε c,
      ∃ s ∈ Icc (ε / 2) b,
        ∀ t ∈ Icc (ε / 2) b, deriv w t ≤ deriv w s)
    (hGen : ∀ y ∈ Ioo ε c,
      X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0)
    (hwUpper : ∀ y ∈ Ioo ε c, q * w y ≤ W)
    (hLoss : ∀ b ∈ Ioo ε c,
      ∀ y ∈ Icc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
        A + η * M) :
    ∀ t ∈ Ico (ε / 2) c,
      deriv w t ≤ max B ((W + A) / (X.drift - η)) := by
  have hLossStrict :
      ∀ b ∈ Ioo ε c, ∀ y ∈ Ioc ε b, ∀ M : ℝ,
        (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
          -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
            A + η * M := by
    intro b hb y hy M hM
    exact hLoss b hb y ⟨le_of_lt hy.1, hy.2⟩ M hM
  have hEnv :
      ∀ b ∈ Ioo ε c, ∀ y ∈ Ioc ε b, ∀ M : ℝ,
        (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
          X.drift * deriv w y ≤ (W + A) + η * M :=
    avram_bva_capHJB45s_original_BV_strict_source_HJB_to_derivative_loss_envelope
      X hBV q w ε c W η A hε hεc hGen hwUpper hLossStrict
  exact avram_bva_capHJB44s_original_BV_derivative_maximum_from_strict_HJB_envelope
    X.drift η (W + A) B ε c hη hε hεc w hLocal hMax hEnv
