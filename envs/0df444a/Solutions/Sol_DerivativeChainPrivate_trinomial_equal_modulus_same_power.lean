-- Prove2me | solution 1 for DerivativeChainPrivate.trinomial_equal_modulus_same_power
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T07:44:19.714688+00:00
-- url     : https://prove2.me/submissions/1c198f38-7578-493f-bdf2-174043dfdef9

import Definitions.Def_DerivativeChainPrivate_foundations
open Filter Topology
open scoped BigOperators
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate



theorem equal_norm_and_distance_one (x y : ℂ) (hnorm : ‖x‖ = ‖y‖)
    (hdist : ‖x - 1‖ = ‖y - 1‖) : x = y ∨ x = starRingEnd ℂ y := by
  have hx := Complex.sq_norm_sub_sq_re x
  have hy := Complex.sq_norm_sub_sq_re y
  have hx1 := Complex.sq_norm_sub_sq_re (x - 1)
  have hy1 := Complex.sq_norm_sub_sq_re (y - 1)
  rw [hnorm] at hx
  rw [hdist] at hx1
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at hx1 hy1
  have hre : x.re = y.re := by nlinarith
  have himsq : x.im ^ 2 = y.im ^ 2 := by nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp himsq with him | him
  · exact Or.inl (Complex.ext hre him)
  · exact Or.inr (Complex.ext hre (by simpa using him))





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem trinomial_equal_modulus_power_eq_or_conj (d e : ℕ) (x y c : ℂ)
    (hy : y ≠ 0) (hnorm : ‖x‖ = ‖y‖)
    (hxroot : x ^ (e - d) * (x ^ d - 1) = c)
    (hyroot : y ^ (e - d) * (y ^ d - 1) = c) :
    x ^ d = y ^ d ∨ x ^ d = starRingEnd ℂ (y ^ d) := by
  have hxp := congrArg norm hxroot
  have hyp := congrArg norm hyroot
  simp only [norm_mul, norm_pow] at hxp hyp
  rw [hnorm] at hxp
  have hnonzero : ‖y‖ ^ (e - d) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hy)
  have hdist : ‖x ^ d - 1‖ = ‖y ^ d - 1‖ :=
    mul_left_cancel₀ hnonzero (hxp.trans hyp.symm)
  apply equal_norm_and_distance_one (x ^ d) (y ^ d) _ hdist
  simp only [norm_pow, hnorm]

theorem trinomial_reflection_phase_constraint (d e : ℕ) (hde : d ≤ e)
    (omega y c : ℂ) (homega : omega ^ d = 1)
    (hyroot : y ^ (e - d) * (y ^ d - 1) = c)
    (hxroot : (omega * starRingEnd ℂ y) ^ (e - d) *
      ((omega * starRingEnd ℂ y) ^ d - 1) = c) :
    c = omega ^ e * starRingEnd ℂ c := by
  have hexp : omega ^ e = omega ^ (e - d) := by
    conv_lhs => rw [← Nat.sub_add_cancel hde, pow_add, homega, mul_one]
  have hstar : (starRingEnd ℂ y) ^ (e - d) * ((starRingEnd ℂ y) ^ d - 1) =
      starRingEnd ℂ c := by
    simpa only [map_mul, map_sub, map_pow, map_one] using congrArg (starRingEnd ℂ) hyroot
  rw [mul_pow, mul_pow, homega, one_mul] at hxroot
  rw [hexp, ← hstar]
  rw [← hxroot]
  ring

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace DerivativeChainPrivate























end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate

theorem trinomial_reflection_excluded (d e m : ℕ) (hdiv : d ∣ e * m)
    (T psi : ℝ) (hT : 0 < T) (hangle : 0 < (m : ℝ) * psi)
    (hanglepi : (m : ℝ) * psi < Real.pi) (omega : ℂ) (homega : omega ^ d = 1) :
    (T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) ≠
      omega ^ e * starRingEnd ℂ ((T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) := by
  intro heq
  let c : ℂ := (T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)
  have homegam : (omega ^ e) ^ m = 1 := by
    obtain ⟨k, hk⟩ := hdiv
    rw [← pow_mul, hk, pow_mul, homega, one_pow]
  have hp : c ^ m = starRingEnd ℂ (c ^ m) := by
    calc
      c ^ m = (omega ^ e * starRingEnd ℂ c) ^ m := congrArg (fun z : ℂ => z ^ m) heq
      _ = (omega ^ e) ^ m * (starRingEnd ℂ c) ^ m := mul_pow _ _ _
      _ = starRingEnd ℂ (c ^ m) := by rw [homegam, one_mul, map_pow]
  have himzero : (c ^ m).im = 0 := by
    have h := congrArg Complex.im hp
    simp only [Complex.conj_im] at h
    linarith
  have hexp : (Complex.exp ((psi : ℂ) * Complex.I)) ^ m =
      Complex.exp (((((m : ℝ) * psi) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have him : (c ^ m).im = T ^ m * Real.sin ((m : ℝ) * psi) := by
    dsimp only [c]
    rw [mul_pow, hexp, ← Complex.ofReal_pow]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  have hpos : 0 < (c ^ m).im := by
    rw [him]
    exact mul_pos (pow_pos hT _) (Real.sin_pos_of_pos_of_lt_pi hangle hanglepi)
  linarith





end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (d e m : ℕ) (hde : d ≤ e)
    (hdiv : d ∣ e * m) (T psi : ℝ) (hT : 0 < T)
    (hangle : 0 < (m : ℝ) * psi) (hanglepi : (m : ℝ) * psi < Real.pi)
    (x y : ℂ) (hy : y ≠ 0) (hnorm : ‖x‖ = ‖y‖)
    (hxroot : x ^ (e - d) * (x ^ d - 1) = (T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))
    (hyroot : y ^ (e - d) * (y ^ d - 1) = (T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) :
    x ^ d = y ^ d := by
  rcases trinomial_equal_modulus_power_eq_or_conj d e x y _ hy hnorm hxroot hyroot with h | h
  · exact h
  · let omega : ℂ := x / starRingEnd ℂ y
    have hconj : starRingEnd ℂ y ≠ 0 := by simpa using hy
    have homega : omega ^ d = 1 := by
      dsimp only [omega]
      rw [div_pow, h, map_pow]
      exact div_self (pow_ne_zero _ hconj)
    have hxeq : x = omega * starRingEnd ℂ y := by
      dsimp only [omega]
      exact (div_mul_cancel₀ x hconj).symm
    have hx := hxroot
    rw [hxeq] at hx
    have hreflect := trinomial_reflection_phase_constraint d e hde omega y _ homega hyroot hx
    exact False.elim ((trinomial_reflection_excluded d e m hdiv T psi hT hangle hanglepi omega homega) hreflect)
