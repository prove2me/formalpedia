-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07a_original_BV_C1_moving_base_right_generator_of_sublinear_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:59:44.90829+00:00
-- url     : https://prove2.me/submissions/e3ebad1a-a6b7-478f-b6ba-a14ea3c80573

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_levy_transition_right_generator_of_global_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_chat07a_original_BV_C1_normalized_semigroup_spatial_stability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x)
    (b : ℝ → ℝ)
    (hb : Tendsto (fun h : ℝ => h⁻¹ * |b h - x|)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, w (b h + X.X (Real.toNNReal h) ω) ∂P) - w (b h)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (X.generator w x)) := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  let f : ℝ → ℝ := fun h =>
    h⁻¹ * ((∫ ω, w (b h + X.X (Real.toNNReal h) ω) ∂P) - w (b h))
  let g : ℝ → ℝ := fun h =>
    h⁻¹ * ((∫ ω, w (x + X.X (Real.toNNReal h) ω) ∂P) - w x)
  have hFixed : Tendsto g F (nhds (X.generator w x)) :=
    bv_levy_transition_right_generator_of_global_C1_lipschitz
      X hX hBV w hwC1 L hL hLip x hgen
  have hpos : ∀ᶠ h : ℝ in F, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in F, h < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hBound : ∀ᶠ h : ℝ in F,
      |f h - g h| ≤ (2 * L) * (h⁻¹ * |b h - x|) := by
    filter_upwards [hpos, hsmall] with h hhp hh1
    have htpos : 0 < Real.toNNReal h := by
      apply NNReal.coe_pos.mp
      simpa [Real.coe_toNNReal, max_eq_left hhp.le] using hhp
    have ht1 : Real.toNNReal h ≤ (1 : ℝ≥0) := by
      apply NNReal.coe_le_coe.mp
      simpa [Real.coe_toNNReal, max_eq_left hhp.le] using le_of_lt hh1
    have hh := avram_chat07a_original_BV_C1_normalized_semigroup_spatial_stability
      X hX hBV w hwC1 L hL hLip x (b h) (Real.toNNReal h) htpos ht1
    simpa [f, g, Real.coe_toNNReal, max_eq_left hhp.le, mul_assoc] using hh
  have hScale : Tendsto
      (fun h : ℝ => (2 * L) * (h⁻¹ * |b h - x|))
      F (nhds (0 : ℝ)) := by
    simpa using hb.const_mul (2 * L)
  have hNorm : Tendsto (fun h : ℝ => ‖f h - g h‖)
      F (nhds (0 : ℝ)) := by
    have hLo (h : ℝ) : 0 ≤ ‖f h - g h‖ := norm_nonneg _
    have hHi : ∀ᶠ h : ℝ in F,
        ‖f h - g h‖ ≤ (2 * L) * (h⁻¹ * |b h - x|) := by
      simpa only [Real.norm_eq_abs] using hBound
    exact squeeze_zero' (Filter.Eventually.of_forall hLo) hHi hScale
  have hZero : Tendsto (fun h : ℝ => f h - g h) F (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hNorm
  have hSum := hZero.add hFixed
  simpa only [sub_add_cancel, zero_add] using hSum
