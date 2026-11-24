-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.prekopa_leindler_1d_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:28.044085+00:00
-- url     : https://prove2.me/submissions/684950c9-ad9b-4938-9e12-ce2e3b5f38ad

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_brunn_minkowski_1d
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_vol_superlevelset_measurable
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_layercake
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_lintegral_eq_vol_superlevelset_lintegral_01
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_weighted_amgm

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f) (hf_sup1 : iSup f = 1)
    (hg_measurable : Measurable g) (hg_sup1 : iSup g = 1)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ (∫⁻ x, h x) := by

  -- {f>t} + {g>t} ⊆ {h>t}
  have h_superlevelset_incl : ∀ t : ℝ, 0 < t →
      {x | ENNReal.ofReal t ≤ f x} + {x | ENNReal.ofReal t ≤ g x}
      ⊆ {x | ENNReal.ofReal t ≤ h x} := by
    intro t ht
    rw [add_subset_iff]
    intro x hx y hy
    simp only [mem_ofPred_eq] at hx hy ⊢
    calc
      ENNReal.ofReal t = (ENNReal.ofReal t) ^ (1 - θ) * (ENNReal.ofReal t) ^ θ := by
        rw [← ENNReal.rpow_add (1-θ) θ (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top]
        simp
      _ ≤ f x ^ (1 - θ) * g y ^ θ := by
        gcongr
        · linarith
        linarith
      _ ≤ h (x + y) := hfgh x y

  -- vol({f>t}) + vol({g>t}) ≤ vol({h>t})
  let vf : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}
  let vg : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ g x}
  let vh : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ h x}

  have h_vol_ineq : ∀ t : ℝ, 0 < t ∧ t < 1 → vf t + vg t ≤ vh t := by
    intro t ht
    have superlevelset_nonempty {f : ℝ → ENNReal} (hf_sup1 : iSup f = 1)
        : {x | ENNReal.ofReal t ≤ f x}.Nonempty := by
      apply nonempty_def.mpr
      suffices ∃ x, x ∈ {x | ENNReal.ofReal t < f x} by
        simp only [mem_ofPred_eq] at this ⊢
        rcases this with ⟨x, hx⟩
        use x
        exact le_of_lt hx
      simp only [mem_ofPred_eq]
      apply exists_lt_of_lt_ciSup
      simp only [hf_sup1, ENNReal.ofReal_lt_one, ht.2]
    exact brunn_minkowski_1d
      (h_superlevelset_incl t ht.1)
      (superlevelset_nonempty hf_sup1) (measurableSet_le measurable_const hf_measurable)
      (superlevelset_nonempty hg_sup1) (measurableSet_le measurable_const hg_measurable)

  -- integrate the volume inequality
  -- ∫_0^1 vol({f>t}) + vol({g>t}) dt ≤ ∫_0^1 vol({h>t}) dt ≤ ∫_0^∞ vol({h>t}) dt
  have h_vol_ineq_integral :
      (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ioo 0 1, vg t) ≤ ∫⁻ t in Ioi 0, vh t := calc
    (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ioo 0 1, vg t)
        = ∫⁻ t in Ioo 0 1, (vf t + vg t) := by
      rw [lintegral_add_left (vol_superlevelset_measurable f)]
    _ ≤ ∫⁻ t in Ioo 0 1, vh t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))]
        with t ht
      exact h_vol_ineq t ht
    _ ≤ ∫⁻ t in Ioi 0, vh t := by apply lintegral_mono_set; grind

  -- "layer cake" formulas
  -- ∫ h = ∫_0^∞ vol({h>t}) dt, ∫ f = ∫_0^1 vol({f>t}) dt, ∫ g = ∫_0^1 vol({g>t}) dt
  let fint : ENNReal := ∫⁻ x, f x
  let gint : ENNReal := ∫⁻ x, g x
  let hint : ENNReal := ∫⁻ x, h x
  have hfint : fint = ∫⁻ t in Ioo 0 1, vf t :=
    have hf_bound : f ≤ 1 := by
      intro x; simp only [Pi.one_apply]; rw [← hf_sup1]; exact le_iSup_iff.mpr fun _ a ↦ a x
    lintegral_eq_vol_superlevelset_lintegral_01 hf_bound hf_measurable
  have hgint : gint = ∫⁻ t in Ioo 0 1, vg t :=
    have hg_bound : g ≤ 1 := by
      intro x; simp only [Pi.one_apply]; rw [← hg_sup1]; exact le_iSup_iff.mpr fun _ a ↦ a x
    lintegral_eq_vol_superlevelset_lintegral_01 hg_bound hg_measurable
  have hhint : hint = ∫⁻ t in Ioi 0, vh t := layercake hh_measurable

  -- implies ∫ f + ∫ g ≤ ∫ h
  have h_ineq_integral : fint + gint ≤ hint := by
    rw [← hhint, ← hfint, ← hgint] at h_vol_ineq_integral
    exact h_vol_ineq_integral

  -- quickly prove the result in the case of fint = ⊤ or gint = ⊤
  by_cases h_fint_eq_top : fint = ⊤
  · simp only [h_fint_eq_top, top_add, top_le_iff] at h_ineq_integral
    unfold fint at h_fint_eq_top; unfold hint at h_ineq_integral
    simp [h_fint_eq_top, h_ineq_integral]
  by_cases h_gint_eq_top : gint = ⊤
  · simp only [h_gint_eq_top, add_top, top_le_iff] at h_ineq_integral
    unfold gint at h_gint_eq_top; unfold hint at h_ineq_integral
    simp [h_gint_eq_top, h_ineq_integral]

  -- now fint and gint are both finite
  have weighted_amgm_factor_nonneg : 0 ≤ ((1-θ)^(1-θ) * θ^θ)⁻¹ := by
    rw [inv_nonneg]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) (1 - θ)) (Real.rpow_nonneg (by linarith) θ)

  calc
    ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * fint^(1-θ) * gint^θ =
        ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * ENNReal.ofReal ((fint^(1-θ)).toReal) * gint^θ := by
      congr; rw [ENNReal.ofReal_toReal]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) h_fint_eq_top
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * ENNReal.ofReal (fint.toReal^(1-θ)) * gint^θ := by
      rw [← ENNReal.toReal_rpow]
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ)) * gint^θ := by
      rw [← ENNReal.ofReal_mul]; exact weighted_amgm_factor_nonneg
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ))
        * ENNReal.ofReal ((gint^θ).toReal) := by
      congr; rw [ENNReal.ofReal_toReal]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) h_gint_eq_top
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ))
        * ENNReal.ofReal (gint.toReal^θ) := by
      rw [← ENNReal.toReal_rpow]
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ) * gint.toReal^θ) := by
      rw [← ENNReal.ofReal_mul]
      exact mul_nonneg weighted_amgm_factor_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg (1-θ))
    _ ≤ ENNReal.ofReal (fint.toReal + gint.toReal) :=
      ENNReal.ofReal_le_ofReal (weighted_amgm hθ ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    _ = ENNReal.ofReal (fint.toReal) + ENNReal.ofReal (gint.toReal) :=
      ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = fint + gint := by simp [h_fint_eq_top, h_gint_eq_top]
    _ ≤ hint := by exact h_ineq_integral
end GaussianPerimeter.VolumeComparison
