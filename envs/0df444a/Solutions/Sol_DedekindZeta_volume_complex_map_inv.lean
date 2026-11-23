-- Prove2me | solution 1 for DedekindZeta.volume_complex_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:28:12.966054+00:00
-- url     : https://prove2.me/submissions/a9f0c355-592d-4387-89c0-b5d3c2628605

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta
theorem _root_.solution :
    Measure.map (fun z : ℂ => z⁻¹) volume
      = volume.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ 4)⁻¹) := by
  set f : ℂ → ℂ := fun z => z⁻¹ with hf_def
  set s : Set ℂ := {(0 : ℂ)}ᶜ with hs_def
  have hs : MeasurableSet s := (measurableSet_singleton 0).compl
  -- the real Fréchet derivative of `z ↦ z⁻¹` at `z` is multiplication by `-z⁻²`,
  -- viewed as the `ℝ`-restriction of a `ℂ`-linear (conformal) map.
  set f' : ℂ → (ℂ →L[ℝ] ℂ) :=
    fun z => (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹)).restrictScalars ℝ
      with hf'_def
  have hmeas : Measurable f := by rw [hf_def]; fun_prop
  -- `|det_ℝ (-z⁻²·)| = ‖-z⁻²‖² = (‖z‖⁴)⁻¹`, valid for every `z` (incl. the null point `0`).
  have hdet : (fun z => ENNReal.ofReal |(f' z).det|)
      = (fun z => ENNReal.ofReal (‖z‖ ^ 4)⁻¹) := by
    funext z
    have hd : (f' z).det = ‖(-(z ^ 2)⁻¹)‖ ^ 2 := by
      rw [hf'_def]
      simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
        Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
    rw [hd, abs_of_nonneg (by positivity)]
    congr 1
    rw [norm_neg, norm_inv, norm_pow, inv_pow, ← pow_mul]
  -- differentiability of `f` on the conull set `s = {0}ᶜ`
  have hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x := by
    intro x hx
    have hx0 : x ≠ 0 := hx
    exact ((hasDerivAt_inv hx0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn f s := by
    intro a _ b _ hab
    simpa [hf_def] using inv_injective hab
  have himg : f '' s = s := by
    rw [hf_def, hs_def]
    ext w
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro hw; exact ⟨w⁻¹, by simpa using hw, inv_inv w⟩
  -- change of variables on `s`: push `volume.restrict s` with the Jacobian density
  -- back to `volume` on the image `s`.
  have key := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure ℂ) hs.nullMeasurableSet hf' hinj
  rw [himg, hdet] at key
  -- `{0}` is `volume`-null, so `volume.restrict s = volume`.
  have hconull : (volume : Measure ℂ).restrict s = volume := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [hs_def]
    exact compl_mem_ae_iff.mpr (measure_singleton 0)
  rw [hconull] at key
  -- `f` is an involution, so applying `map f` to `key` inverts it.
  have hinvol : f ∘ f = id := by funext z; simp [hf_def, inv_inv]
  have hres := congrArg (Measure.map f) key
  rw [Measure.map_map hmeas hmeas, hinvol, Measure.map_id] at hres
  exact hres.symm
end DedekindZeta
