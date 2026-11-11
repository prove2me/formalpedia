-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_original_finite_cap_derivative_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:52:12.835653+00:00
-- url     : https://prove2.me/submissions/a456a7e3-b54b-43da-8a4f-7a5b2cffe234

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_finite_jump_generator_lower
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_hjb_diff_comparison
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_cap_ode_derivative_uniform
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Finite negative-mark intensity supplies a near-cap derivative bound via HJB and ODE comparison. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q jumpRate W u C β ε : ℝ)
    (hu : 0 < u) (huC : u < C) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hA : 0 < X.σ ^ 2 / 2)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hJumpRate : jumpRate = (X.ν (Iio (0 : ℝ))).toReal)
    (hQ : 0 ≤ q + jumpRate)
    (hSmooth : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hDeriv : ∀ y ∈ Ico u C, 0 ≤ deriv w y)
    (hReward : ∀ y ∈ Ico u C, ∀ t : ℝ, t ≤ y → 0 ≤ w t)
    (hUpper : ∀ y ∈ Ico u C, w y ≤ W)
    (hHJB : ∀ y ∈ Ico u C,
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hBeta : -X.c ≤ (X.σ ^ 2 / 2) * β)
    (hEps : (q + jumpRate) * W ≤ (X.σ ^ 2 / 2) * ε) :
    ∃ B : ℝ, ∀ y ∈ Ico u C, deriv w y ≤ B := by
  have hSubset : Ico u C ⊆ Ioo (0 : ℝ) C := by
    intro y hy
    exact ⟨lt_of_lt_of_le hu hy.1, hy.2⟩
  have hC1 : ContDiffOn ℝ 1 (deriv w) (Ioo (0 : ℝ) C) :=
    hSmooth.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hPcont : ContinuousOn (deriv w) (Ico u C) :=
    hC1.continuousOn.mono hSubset
  have hPderiv : ∀ y ∈ Ico u C,
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y := by
    intro y hy
    have hi : y ∈ Ioo (0 : ℝ) C := hSubset hy
    have hd : DifferentiableAt ℝ (deriv w) y :=
      (hC1.differentiableOn_one y hi).differentiableAt (isOpen_Ioo.mem_nhds hi)
    simpa [iteratedDeriv_succ] using hd.hasDerivAt
  have hODE : ∀ y ∈ Ico u C,
      iteratedDeriv 2 w y ≤ β * deriv w y + ε := by
    intro y hy
    have hJump : -jumpRate * w y ≤
        ∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
      simpa [hJumpRate] using
        (avram_mix_fin26_finite_jump_generator_lower X w y hFinite
          (hHJB y hy).1 (hReward y hy) (hDeriv y hy))
    exact avram_mix_fin26_hjb_diff_comparison X w q jumpRate W β ε y
      hA hJump (hHJB y hy).2 (hUpper y hy) hQ hBeta hEps (hDeriv y hy)
  exact avram_gauss_finitec2_cap_ode_derivative_uniform
    (deriv w) (iteratedDeriv 2 w) u C β ε huC hβ hε
    (hDeriv u ⟨le_rfl, huC⟩) hPcont hPderiv hODE
