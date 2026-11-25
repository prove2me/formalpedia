-- Prove2me | solution 1 for Formalism.QuantumDeterminants.adjoint_functional_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:19:29.134875+00:00
-- url     : https://prove2.me/submissions/1e746c63-3bd5-442e-bada-91c4f88c3526

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_isOpen_OmX
import Theorems.Thm_Formalism_QuantumDeterminants_wirt_mul_fun
import Theorems.Thm_Formalism_QuantumDeterminants_wirt_star_fun
import Theorems.Thm_Formalism_QuantumDeterminants_uW_contDiffOn
import Theorems.Thm_Formalism_QuantumDeterminants_wirt_uW
import Theorems.Thm_Formalism_QuantumDeterminants_tsupport_star_fun
import Theorems.Thm_Formalism_QuantumDeterminants_integrable_of_on

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}
namespace Formalism.QuantumDeterminants
theorem _root_.solution : AdjFun := by
  intro m l f g hf hg hfc hgc hfΩ hgΩ
  have hΩo := isOpen_OmX m
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  set h : (Fin m → ℂ) → ℂ := fun y => star (g y) * uW l y with hh
  have hsg : ContDiffOn ℝ ∞ (fun y => star (g y)) (OmX m) := by
    have h1 := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hg1
    convert h1 using 1
    funext y
    simp
  have hhc : ContDiffOn ℝ ∞ h (OmX m) := hsg.mul (uW_contDiffOn l)
  have hfd : ∀ x ∈ OmX m, DifferentiableAt ℝ f x := fun x hx =>
    (hf1.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)
  have hgd : ∀ x ∈ OmX m, DifferentiableAt ℝ g x := fun x hx =>
    (hg1.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)
  have hud : ∀ x ∈ OmX m, DifferentiableAt ℝ (uW l) x := fun x hx =>
    ((uW_contDiffOn l).differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)
  have hhd : ∀ x ∈ OmX m, DifferentiableAt ℝ h x := fun x hx =>
    (hhc.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)
  have hhg : tsupport h ⊆ tsupport g := by
    have h1 : tsupport h ⊆ tsupport (fun y => star (g y)) := tsupport_mul_subset_left
    rwa [tsupport_star_fun] at h1
  have hhΩ : tsupport h ⊆ OmX m := hhg.trans hgΩ
  have hhK : HasCompactSupport h := IsCompact.of_isClosed_subset hgc (isClosed_tsupport _) hhg
  have hfz : ∀ x, x ∉ OmX m → fderiv ℝ f x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport f := fun h' => hx (hfΩ h')
    by_contra hne
    exact hx' (support_fderiv_subset ℝ hne)
  have hL : ∀ x, pOp l f x * star (g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) =
      wirt l f x * h x := by
    intro x
    by_cases hx : x ∈ OmX m
    · simp only [pOp, if_pos hx, smul_eq_mul, hh, uW]
      ring
    · simp [pOp, hx, wirt, hfz x hx]
  have hR : ∀ x, f x * star (pbOp l g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) =
      f x * wirt l h x := by
    intro x
    by_cases hx : x ∈ OmX m
    · have hsd : DifferentiableAt ℝ (fun y => star (g y)) x := (hgd x hx).star
      rw [hh, wirt_mul_fun l hsd (hud x hx), wirt_uW l x hx, wirt_star_fun]
      simp only [pbOp, if_pos hx, smul_eq_mul, star_mul', star_star, uW]
      ring
    · simp [hf2 x hx]
  have eL : (∫ x, pOp l f x * star (g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) =
      ∫ x, wirt l f x * h x := by
    congr 1
    funext x
    exact hL x
  have eR : (∫ x, f x * star (pbOp l g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) =
      ∫ x, f x * wirt l h x := by
    congr 1
    funext x
    exact hR x
  rw [eL, eR]
  have I1 : ∀ v, Integrable (fun x => fderiv ℝ f x v * h x) := by
    intro v
    refine integrable_of_on ?_ tsupport_mul_subset_right hhK hhΩ
    exact ((hf1.continuousOn_fderiv_of_isOpen hΩo (by simp)).clm_apply continuousOn_const).mul
      hhc.continuousOn
  have I2 : ∀ v, Integrable (fun x => f x * fderiv ℝ h x v) := by
    intro v
    refine integrable_of_on ?_ tsupport_mul_subset_left hfc hfΩ
    exact hf1.continuousOn.mul
      ((hhc.continuousOn_fderiv_of_isOpen hΩo (by simp)).clm_apply continuousOn_const)
  have I3 : Integrable (fun x => f x * h x) :=
    integrable_of_on (hf1.continuousOn.mul hhc.continuousOn) tsupport_mul_subset_left hfc hfΩ
  have ibp : ∀ v, ∫ x, f x * fderiv ℝ h x v = -∫ x, fderiv ℝ f x v * h x := by
    intro v
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (I1 v) (I2 v) I3
      (fun x hx => hfd x (hhΩ hx)) (fun x hx => hhd x (hfΩ hx))
  have hw : ∀ φ : (Fin m → ℂ) → ℂ, ∀ x, wirt l φ x = (1 / 2 : ℂ) *
      (fderiv ℝ φ x (Pi.single l 1) - Complex.I * fderiv ℝ φ x (Pi.single l Complex.I)) := by
    intro φ x
    simp [wirt, smul_eq_mul]
  simp_rw [hw]
  have lhs : (∫ x, (1 / 2 : ℂ) * (fderiv ℝ f x (Pi.single l 1) -
      Complex.I * fderiv ℝ f x (Pi.single l Complex.I)) * h x) =
      (1 / 2 : ℂ) * (∫ x, fderiv ℝ f x (Pi.single l 1) * h x) -
        ((1 / 2 : ℂ) * Complex.I) * ∫ x, fderiv ℝ f x (Pi.single l Complex.I) * h x := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((I1 _).const_mul _) ((I1 _).const_mul _)]
    congr 1
    funext x
    ring
  have rhs : (∫ x, f x * ((1 / 2 : ℂ) * (fderiv ℝ h x (Pi.single l 1) -
      Complex.I * fderiv ℝ h x (Pi.single l Complex.I)))) =
      (1 / 2 : ℂ) * (∫ x, f x * fderiv ℝ h x (Pi.single l 1)) -
        ((1 / 2 : ℂ) * Complex.I) * ∫ x, f x * fderiv ℝ h x (Pi.single l Complex.I) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((I2 _).const_mul _) ((I2 _).const_mul _)]
    congr 1
    funext x
    ring
  rw [lhs, rhs, ibp, ibp]
  ring
end Formalism.QuantumDeterminants
