-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.lintegral_eq_vol_superlevelset_lintegral_01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:20:27.564021+00:00
-- url     : https://prove2.me/submissions/4842d434-3f4a-4547-8825-67fbffa587df

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_vol_superlevelset_measurable
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_layercake

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {f : ℝ → ENNReal} (hf_bound : f ≤ 1) (hf_measurable : Measurable f)
    : ∫⁻ x, f x = ∫⁻ t in Ioo 0 1, (fun t ↦ volume {x | ENNReal.ofReal t ≤ f x}) t := by
  let vf := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}
  calc
    ∫⁻ x, f x = ∫⁻ t in Ioi 0, vf t := layercake hf_measurable
    _ = ∫⁻ t in (Ioo 0 1 ∪ Ici 1), vf t := by simp
    _ = (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ici 1, vf t) :=
      lintegral_union measurableSet_Ici (by simp [disjoint_left])
    _ = ∫⁻ t in Ioo 0 1, vf t := by
      suffices ∫⁻ t in Ici 1, vf t = 0 by simp [this]
      rw [setLIntegral_eq_zero_iff measurableSet_Ici (vol_superlevelset_measurable f)]
      suffices ∀ x : ℝ, x ∈ Ioi 1 → volume {x_1 | ENNReal.ofReal x ≤ f x_1} = 0 by
        apply ae_of_mem_of_ae_of_mem_inter_Ioo; intros; filter_upwards; intro c _
        simp_all only [mem_Ioi, mem_Ici, mem_inter_iff, mem_Ioo]
        exact this c (by linarith)
      intro a ha
      suffices {x | ENNReal.ofReal a ≤ f x} = ∅ by rw [this]; exact measure_empty
      apply eq_empty_of_forall_notMem
      intro x hx
      have : 1 < f x := calc
        1 < ENNReal.ofReal a := ENNReal.one_lt_ofReal.mpr ha
        _ ≤ f x := hx
      exact absurd this (not_lt.mpr (hf_bound x))
end GaussianPerimeter.VolumeComparison
