-- Prove2me | solution 1 for FiniteEnergyPlane.norm_sub_le_of_norm_mul_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T21:09:35.902254+00:00
-- url     : https://prove2.me/submissions/fcbaac86-110b-40ce-9cca-3f51632d858a

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

/-- Oscillation on circles: let `f : ℂ → E` be differentiable on the punctured disc `0 < |z| < R`
with `|z| ‖Df(z)‖ ≤ η` there. Then any two points `z, w` on a common circle `|z| = |w| < R`
around the origin satisfy `‖f z - f w‖ ≤ π η`. -/
theorem norm_sub_le_of_norm_mul_fderiv_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R η : ℝ)
    (hf : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → DifferentiableAt ℝ f z ∧ ‖z‖ * ‖fderiv ℝ f z‖ ≤ η) :
    ∀ z w : ℂ, z ≠ 0 → ‖z‖ < R → ‖w‖ = ‖z‖ → ‖f z - f w‖ ≤ π * η := by
  intro z w hz hzR hw
  have hη : 0 ≤ η := le_trans (by positivity) (hf z hz hzR).2
  set θ : ℝ := Complex.arg (w / z) with hθ
  have hθπ : |θ| ≤ π := Complex.abs_arg_le_pi _
  have hwz : ‖w / z‖ = 1 := by
    rw [norm_div, hw, div_self (norm_ne_zero_iff.mpr hz)]
  have hwexp : w = z * Complex.exp (θ * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (w / z)
    rw [hwz, Complex.ofReal_one, one_mul] at h
    rw [← hθ] at h
    rw [h]; field_simp
  -- the arc `t ↦ z exp(t θ i)`, `t ∈ [0, 1]`
  set p : ℝ → ℂ := fun t => z * Complex.exp (t * (θ * Complex.I)) with hp
  have hpn : ∀ t : ℝ, ‖p t‖ = ‖z‖ := by
    intro t
    simp only [hp, norm_mul]
    rw [show (t : ℂ) * (θ * Complex.I) = ((t * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hpd : ∀ t : ℝ, HasDerivAt p (p t * (θ * Complex.I)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (θ * Complex.I)) (1 * (θ * Complex.I)) t :=
      (hasDerivAt_id t).ofReal_comp.mul_const _
    have h2 := (h1.cexp).const_mul z
    simpa [hp, mul_assoc] using h2
  have hp0 : ∀ t : ℝ, p t ≠ 0 := fun t => by
    rw [← norm_ne_zero_iff, hpn]; exact norm_ne_zero_iff.mpr hz
  have hcomp : ∀ t : ℝ, HasDerivAt (f ∘ p) (fderiv ℝ f (p t) (p t * (θ * Complex.I))) t := by
    intro t
    exact ((hf (p t) (hp0 t) (by rw [hpn]; exact hzR)).1.hasFDerivAt).comp_hasDerivAt t (hpd t)
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖fderiv ℝ f (p t) (p t * (θ * Complex.I))‖ ≤ π * η := by
    intro t _
    have hb := (hf (p t) (hp0 t) (by rw [hpn]; exact hzR)).2
    calc ‖fderiv ℝ f (p t) (p t * (θ * Complex.I))‖
        ≤ ‖fderiv ℝ f (p t)‖ * ‖p t * (θ * Complex.I)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = (‖p t‖ * ‖fderiv ℝ f (p t)‖) * |θ| := by
          rw [norm_mul, hpn, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          ring
      _ ≤ η * π := mul_le_mul hb hθπ (abs_nonneg _) hη
      _ = π * η := mul_comm _ _
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f ∘ p)
    (fun t _ => (hcomp t).hasDerivWithinAt) hbound 1 (by simp)
  have hp1 : p 1 = w := by rw [hwexp]; simp [hp]
  have hp0' : p 0 = z := by simp [hp]
  simp only [Function.comp_apply, hp1, hp0', sub_zero, mul_one] at hmvt
  rw [norm_sub_rev]; exact hmvt

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R η : ℝ)
    (hf : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → DifferentiableAt ℝ f z ∧ ‖z‖ * ‖fderiv ℝ f z‖ ≤ η) :
    ∀ z w : ℂ, z ≠ 0 → ‖z‖ < R → ‖w‖ = ‖z‖ → ‖f z - f w‖ ≤ π * η :=
  FiniteEnergyPlane.norm_sub_le_of_norm_mul_fderiv_le_aux f R η hf
