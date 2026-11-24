-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.lintegral_fix_lintegral_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:23.385424+00:00
-- url     : https://prove2.me/submissions/baecb72b-bfc0-4882-908f-f66ffc42e84f

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_lintegral_fin1
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_append_measurable
public import Theorems.Thm_P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_fix_measurable
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable'
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.fix_measurable

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {d : ℕ} {f : (Fin (d + 2) → ℝ) → ENNReal} (hf_measurable : Measurable f) :
    ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : Fin 1 → ℝ), (fix f x) t
    = ∫⁻ (x : Fin (d + 2) → ℝ), f x := by
  -- This proof works by rewriting the LHS until we can use the volume preserving
  -- measurable equivalence for piFinSuccAbove in mathlib.

  -- Rewrite the integral over Fin 1 → ℝ as an integral over ℝ
  have : ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : Fin 1 → ℝ), (fix f x) t
      = ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : ℝ), f (append x (fun _ ↦ t)) := by
    congr; ext; rw [lintegral_fin1]; rfl
  rw [this]

  -- Rewrite the iterated integral ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : ℝ) ...
  -- as a single integral over ℝ × (Fin (d + 1) → ℝ). The order is swapped for compatibility with
  -- MeasurableEquiv.piFinSuccAbove.
  let equiv : (Fin (d + 2) → ℝ) ≃ᵐ ℝ × (Fin (d + 1) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 2) ↦ ℝ) (Fin.last (d + 1))
  let g : ℝ × (Fin (d + 1) → ℝ) → (Fin (d + 2) → ℝ) := fun tx ↦ (append tx.2 fun _ ↦ tx.1)
  have hg_eq_equiv_invFun : g = equiv.invFun := by aesop
  have hg_measurable : Measurable g := by rw [hg_eq_equiv_invFun]; exact equiv.measurable_invFun
  let f' : (ℝ × (Fin (d + 1) → ℝ)) → ENNReal := fun tx ↦ f (append tx.2 fun x ↦ tx.1)
  have hf'_measurable : Measurable f' := by
    apply Measurable.comp hf_measurable; unfold g at hg_measurable; exact hg_measurable
  rw [← MeasureTheory.lintegral_prod_symm' f' hf'_measurable]

  -- Clean up ∂volume.prod volume from lintegral_prod_symm'
  have : ∫⁻ (z : ℝ × (Fin (d + 1) → ℝ)), f' z ∂volume.prod volume
    = ∫⁻ (z : ℝ × (Fin (d + 1) → ℝ)), f' z := by rfl
  rw [this]

  -- Rewrite the integral over ℝ × (Fin (d + 1) → ℝ as an integral over Fin (d + 2) → ℝ
  rw [← MeasureTheory.lintegral_map hf_measurable hg_measurable]
  -- Use the fact that the equivalence is volume preserving
  congr
  rw [hg_eq_equiv_invFun]
  exact (MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (d + 2) ↦ ℝ) (Fin.last (d + 1))).symm.map_eq
end GaussianPerimeter.VolumeComparison
