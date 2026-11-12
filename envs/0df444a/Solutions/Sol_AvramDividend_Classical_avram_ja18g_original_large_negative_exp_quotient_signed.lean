-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_large_negative_exp_quotient_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:08:33.460532+00:00
-- url     : https://prove2.me/submissions/9ddd3fa0-7221-4ced-8882-bfe0b3b82fd5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_signed_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_scalar_exponential_quotient_right_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original large-negative Lévy marks admit exponential-quotient dominated convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Filter.Tendsto
      (fun θ : ℝ =>
        (∫ z in Iic (-1 : ℝ), Real.exp (θ * z) - 1 ∂X.ν) / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ z in Iic (-1 : ℝ), z ∂X.ν)) := by
  let B : Set ℝ := Iic (-1 : ℝ)
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  let F : ℝ → ℝ → ℝ := fun θ z => (Real.exp (θ * z) - 1) / θ
  have hFmeas : ∀ᶠ θ in l,
      AEStronglyMeasurable (F θ) (X.ν.restrict B) := by
    exact Filter.Eventually.of_forall (fun θ => by
      dsimp [F]
      fun_prop)
  have hKint : Integrable (fun z : ℝ => |z|) (X.ν.restrict B) := by
    simpa only [B, Real.norm_eq_abs] using
      (avram_ja18g_original_large_negative_signed_mark_integrable X hX).norm
  have hpos : ∀ᶠ θ in l, 0 < θ := by
    filter_upwards [self_mem_nhdsWithin] with θ hθpos
    exact hθpos
  have hDom : ∀ᶠ θ in l,
      ∀ᵐ z ∂X.ν.restrict B, ‖F θ z‖ ≤ |z| := by
    filter_upwards [hpos] with θ hθpos
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
    have hzneg : z ≤ 0 := le_trans hz (by norm_num)
    have htz : θ * z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθpos.le hzneg
    have he : Real.exp (θ * z) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr htz
    have he' : 1 - Real.exp (θ * z) ≤ -(θ * z) := by
      nlinarith [Real.add_one_le_exp (θ * z)]
    dsimp [F]
    rw [abs_div, abs_of_pos hθpos,
      abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonpos hzneg]
    apply (div_le_iff₀ hθpos).2
    nlinarith [he']
  have hPoint : ∀ᵐ z ∂X.ν.restrict B,
      Tendsto (fun θ => F θ z) l (nhds z) := by
    exact Filter.Eventually.of_forall (fun z => by
      exact avram_ja18g_scalar_exponential_quotient_right_tendsto z)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := X.ν.restrict B) (fun z : ℝ => |z|)
    hFmeas hDom hKint hPoint
  simpa only [F, B, integral_div] using hDCT
