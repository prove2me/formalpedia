-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.exterior_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:27.748974+00:00
-- url     : https://prove2.me/submissions/b55ce9d6-dc10-4fa4-820a-a224d7c8d8f9

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_SLP_Final_sesqDet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.ExtPowerBound := by
  intro j m A A' Z hyp
  let B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun x y => ∑ a, ∑ b, (A *ᵥ x.ofLp) a * Z a b * star ((A' *ᵥ y.ofLp) b))
      (by
        intro x x' y
        simp only [WithLp.ofLp_add, Matrix.mulVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
      (by
        intro c x y
        simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum, mul_assoc])
      (by
        intro x y y'
        simp only [WithLp.ofLp_add, Matrix.mulVec_add, Pi.add_apply, star_add, mul_add,
          Finset.sum_add_distrib])
      (by
        intro c x y
        simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, star_mul',
          Finset.mul_sum, starRingEnd_apply]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        ring)
  have hBdef : ∀ x y, B x y = ∑ a, ∑ b, (A *ᵥ x.ofLp) a * Z a b * star ((A' *ᵥ y.ofLp) b) :=
    fun _ _ => rfl
  have hB1 : ∀ x y : EuclideanSpace ℂ (Fin m), ‖x‖ = 1 → ‖y‖ = 1 → ‖B x y‖ ≤ 2 := by
    intro x y hx hy
    rw [hBdef]
    apply hyp
    · have := EuclideanSpace.norm_sq_eq x
      rw [hx] at this
      simpa using this.symm.le
    · have := EuclideanSpace.norm_sq_eq y
      rw [hy] at this
      simpa using this.symm.le
  have hB : ∀ x y, ‖B x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    have h1 := hB1 (((‖x‖ : ℂ))⁻¹ • x) (((‖y‖ : ℂ))⁻¹ • y)
      (by rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hx0])
      (by rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hy0])
    have e0 : B (((‖x‖ : ℂ))⁻¹ • x) (((‖y‖ : ℂ))⁻¹ • y) = (((‖x‖ : ℂ))⁻¹ * ((‖y‖ : ℂ))⁻¹) * B x y := by
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_inv₀, Complex.conj_ofReal,
        RingHom.id_apply]
      ring
    rw [e0, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, norm_norm,
      norm_norm] at h1
    have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hyp' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have e : ‖x‖⁻¹ * ‖y‖⁻¹ * ‖B x y‖ = ‖B x y‖ / (‖x‖ * ‖y‖) := by field_simp
    rw [e, div_le_iff₀ (by positivity)] at h1
    linarith
  let u : Fin j → EuclideanSpace ℂ (Fin m) := fun i => WithLp.toLp 2 (fun l => star (A i l))
  let w : Fin j → EuclideanSpace ℂ (Fin m) := fun i => WithLp.toLp 2 (fun l => star (A' i l))
  have hgram : ∀ (M : Matrix (Fin j) (Fin m) ℂ),
      Matrix.gram ℂ (fun i => (WithLp.toLp 2 (fun l => star (M i l)) : EuclideanSpace ℂ (Fin m))) = M * Mᴴ := by
    intro M
    ext i k
    rw [Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    simp [Matrix.conjTranspose_apply, mul_comm]
  have hmv : ∀ (M : Matrix (Fin j) (Fin m) ℂ) (i a : Fin j),
      (M *ᵥ (fun l => star (M i l))) a = (M * Mᴴ) a i := by
    intro M i a
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hmat : (Matrix.of fun i k => B (u i) (w k)) = (A * Aᴴ)ᵀ * Z * ((A' * A'ᴴ)ᴴ)ᵀ := by
    ext i k
    simp only [Matrix.of_apply, hBdef, u, w, hmv]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply (M := (A * Aᴴ)ᵀ), Matrix.transpose_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  have h := Formalism.SLP.Final.sesqDet _ _ B 2 hB j u w
  rw [hmat, hgram A, hgram A', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
    Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star] at h
  set p := ‖(A * Aᴴ).det‖ with hp
  set q := ‖(A' * A'ᴴ).det‖ with hq
  set z := ‖Z.det‖ with hz
  have hp0 : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := norm_nonneg _
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt hp0, Real.sq_sqrt hq0, ← pow_mul, mul_comm j 2]
  by_cases hpq : p * q = 0
  · rw [hpq, zero_mul]; positivity
  · have hpos : 0 < p * q := lt_of_le_of_ne (mul_nonneg hp0 hq0) (Ne.symm hpq)
    apply le_of_mul_le_mul_left _ hpos
    calc p * q * (p * q * z ^ 2) = (p * z * q) ^ 2 := by ring
      _ ≤ 2 ^ (2 * j) * p * q := h
      _ = p * q * 2 ^ (2 * j) := by ring
end Formalism.HermitianLatticeCounting.P
