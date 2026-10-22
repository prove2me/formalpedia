-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_normalization_contact_identity
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T04:39:51.511874+00:00
-- url     : https://prove2.me/submissions/e1ae0989-a1e8-47d2-b368-68df55a59c09

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Tactic

namespace BirkhoffGlobalSection

open scoped ContDiff

lemma phaseNormSq_pos_of_ne_zero (y : Phase) (hy : y ≠ 0) :
    0 < zNormSq y + wNormSq y := by
  by_contra hn
  have hz : zNormSq y + wNormSq y ≤ 0 := le_of_not_gt hn
  apply hy
  unfold zNormSq wNormSq at hz
  have h0 : y 0 = 0 := sq_eq_zero_iff.mp (by
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)])
  have h1 : y 1 = 0 := sq_eq_zero_iff.mp (by
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)])
  have h2 : y 2 = 0 := sq_eq_zero_iff.mp (by
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)])
  have h3 : y 3 = 0 := sq_eq_zero_iff.mp (by
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)])
  ext i
  fin_cases i <;> assumption

lemma phaseNormSq_contDiff :
    ContDiff ℝ ∞ (fun y : Phase => zNormSq y + wNormSq y) := by
  unfold zNormSq wNormSq
  fun_prop

lemma radialNormalize_contDiffAt (y : Phase) (hy : 0 < zNormSq y + wNormSq y) :
    ContDiffAt ℝ ∞ radialNormalize y := by
  have hs : ContDiffAt ℝ ∞ (fun x : Phase => Real.sqrt (zNormSq x + wNormSq x)) y :=
    phaseNormSq_contDiff.contDiffAt.sqrt (ne_of_gt hy)
  have hi := hs.inv (ne_of_gt (Real.sqrt_pos.2 hy))
  exact hi.smul contDiffAt_id

lemma radialNormalize_smooth_off_zero (y : Phase) (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ radialNormalize y :=
  radialNormalize_contDiffAt y (phaseNormSq_pos_of_ne_zero y hy)

lemma radialNormalize_neg (y : Phase) : radialNormalize (-y) = -radialNormalize y := by
  simp [radialNormalize, zNormSq, wNormSq, smul_neg]

lemma radialNormalize_mem_sphere (y : Phase) (hy : 0 < zNormSq y + wNormSq y) :
    radialNormalize y ∈ unitThreeSphere := by
  change zNormSq (radialNormalize y) + wNormSq (radialNormalize y) = 1
  have hs : Real.sqrt (zNormSq y + wNormSq y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy)
  have hsq := Real.sq_sqrt (le_of_lt hy)
  simp only [radialNormalize, zNormSq, wNormSq, Pi.smul_apply, smul_eq_mul] at *
  field_simp
  nlinarith

lemma phaseRadialContact_scaling (y v : Phase) (r d : ℝ) :
    phaseRadialContact (r • y) (r • v + d • y) = r ^ 2 * phaseRadialContact y v := by
  simp only [phaseRadialContact, phaseSymplecticForm, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]
  ring

lemma radialNormalize_fderiv (y v : Phase) (hy : 0 < zNormSq y + wNormSq y) :
    fderiv ℝ radialNormalize y v =
      (Real.sqrt (zNormSq y + wNormSq y))⁻¹ • v +
        (fderiv ℝ (fun x : Phase => (Real.sqrt (zNormSq x + wNormSq x))⁻¹) y v) • y := by
  have hs : ContDiffAt ℝ ∞ (fun x : Phase => Real.sqrt (zNormSq x + wNormSq x)) y :=
    phaseNormSq_contDiff.contDiffAt.sqrt (ne_of_gt hy)
  have hi := hs.inv (ne_of_gt (Real.sqrt_pos.2 hy))
  have hd := hi.differentiableAt (by simp)
  have hf := hd.hasFDerivAt.smul (hasFDerivAt_id y)
  have he := congrArg (fun L : Phase →L[ℝ] Phase => L v) hf.fderiv
  exact he

lemma radialNormalize_contact (y v : Phase) (hy : 0 < zNormSq y + wNormSq y) :
    phaseRadialContact (radialNormalize y) (fderiv ℝ radialNormalize y v) =
      phaseRadialContact y v / (zNormSq y + wNormSq y) := by
  rw [radialNormalize_fderiv y v hy]
  change phaseRadialContact
    ((Real.sqrt (zNormSq y + wNormSq y))⁻¹ • y) _ = _
  rw [phaseRadialContact_scaling, inv_pow, Real.sq_sqrt hy.le]
  ring

lemma radialNormalize_contact_of_ne_zero (y v : Phase) (hy : y ≠ 0) :
    phaseRadialContact (radialNormalize y) (fderiv ℝ radialNormalize y v) =
      phaseRadialContact y v / (zNormSq y + wNormSq y) :=
  radialNormalize_contact y v (phaseNormSq_pos_of_ne_zero y hy)

lemma radialNormalize_contact_pos (y v : Phase) (hy : 0 < zNormSq y + wNormSq y)
    (hv : 0 < phaseRadialContact y v) :
    0 < phaseRadialContact (radialNormalize y) (fderiv ℝ radialNormalize y v) := by
  rw [radialNormalize_contact y v hy]
  exact div_pos hv hy

lemma radialNormalize_comp_contact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → Phase) (u v : E) (hf : DifferentiableAt ℝ f u)
    (hu : 0 < zNormSq (f u) + wNormSq (f u)) :
    phaseRadialContact (radialNormalize (f u))
      (fderiv ℝ (radialNormalize ∘ f) u v) =
        phaseRadialContact (f u) (fderiv ℝ f u v) / (zNormSq (f u) + wNormSq (f u)) := by
  rw [fderiv_comp u ((radialNormalize_contDiffAt (f u) hu).differentiableAt (by simp)) hf]
  exact radialNormalize_contact (f u) (fderiv ℝ f u v) hu

end BirkhoffGlobalSection

open BirkhoffGlobalSection
open scoped ContDiff

theorem solution
    (y : Phase) (hy : 0 < zNormSq y + wNormSq y) :
    ContDiffAt ℝ ∞ radialNormalize y ∧
      radialNormalize y ∈ unitThreeSphere ∧
      radialNormalize (-y) = -radialNormalize y ∧
      ∀ v : Phase,
        phaseRadialContact (radialNormalize y) (fderiv ℝ radialNormalize y v) =
          phaseRadialContact y v / (zNormSq y + wNormSq y)  := by
  exact ⟨radialNormalize_contDiffAt y hy, radialNormalize_mem_sphere y hy,
    radialNormalize_neg y, fun v => radialNormalize_contact y v hy⟩
