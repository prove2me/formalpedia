-- Prove2me | solution 1 for Complex.exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0347c9cc-a9cc-50b9-b5e8-c720aa21d87d

import Mathlib
import Theorems.Thm_Complex_exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re

set_option autoImplicit false

namespace Ws31
namespace Digamma

open Complex

theorem digamma_add_nat (s₀ : ℂ) (h : 0 < s₀.re) (n : ℕ) :
    digamma (s₀ + n) = digamma s₀ + ∑ k ∈ Finset.range n, (s₀ + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : ∀ m : ℕ, s₀ + n ≠ -(m : ℂ) := by
      intro m heq
      have := congrArg Complex.re heq
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc, digamma_apply_add_one (s₀ + n) hne, ih, add_assoc]

theorem norm_sum_inv_le_harmonic (s₀ : ℂ) (h : 1 ≤ s₀.re) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, (s₀ + (k : ℂ))⁻¹‖ ≤ (harmonic n : ℝ) := by
  have hcast : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹ := by
    simp [harmonic]
  rw [hcast]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hre : (k : ℝ) + 1 ≤ (s₀ + (k : ℂ)).re := by simp; linarith
  have hpos : 0 < (k : ℝ) + 1 := by positivity
  rw [norm_inv]
  exact inv_anti₀ hpos (hre.trans (Complex.re_le_norm _))

theorem one_le_two_mul_log_two_add (x : ℝ) (hx : 0 ≤ x) : 1 ≤ 2 * Real.log (2 + x) := by
  have h1 : Real.log 2 ≤ Real.log (2 + x) := Real.log_le_log (by norm_num) (by linarith)
  have h2 := Real.log_two_gt_d9
  linarith

theorem log_two_add_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.log (2 + x) :=
  Real.log_nonneg (by linarith)

theorem digamma_halfplane (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → ‖digamma s‖ ≤ C * Real.log (2 + ‖s‖) := by
  obtain ⟨C₀, hC₀, H⟩ :=
    Complex.exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
      (min δ 1) (lt_min hδ one_pos)
  refine ⟨C₀ + 3, by linarith, fun s hs => ?_⟩
  have hn0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hL0 := log_two_add_nonneg ‖s‖ hn0
  have hL1 := one_le_two_mul_log_two_add ‖s‖ hn0
  have him : Real.log (2 + |s.im|) ≤ Real.log (2 + ‖s‖) :=
    Real.log_le_log (by positivity) (by linarith [Complex.abs_im_le_norm s])
  by_cases h2 : s.re ≤ 2
  · have h := (H s ((min_le_left δ 1).trans hs) h2).1
    calc ‖digamma s‖ ≤ C₀ * Real.log (2 + |s.im|) := h
      _ ≤ C₀ * Real.log (2 + ‖s‖) := mul_le_mul_of_nonneg_left him hC₀.le
      _ ≤ (C₀ + 3) * Real.log (2 + ‖s‖) := by nlinarith
  · push_neg at h2

    have hre0 : 0 ≤ s.re := by linarith
    set n : ℕ := ⌊s.re⌋₊ - 1 with hn
    have hfl : (⌊s.re⌋₊ : ℝ) ≤ s.re := Nat.floor_le hre0
    have hfl' : s.re < (⌊s.re⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s.re
    have h2fl : 2 ≤ ⌊s.re⌋₊ := Nat.le_floor (by exact_mod_cast h2.le)
    have hncast : (n : ℝ) = (⌊s.re⌋₊ : ℝ) - 1 := by
      rw [hn, Nat.cast_sub (by omega), Nat.cast_one]
    set s₀ : ℂ := s - (n : ℂ) with hs₀
    have hs₀re : s₀.re = s.re - n := by simp [hs₀]
    have h1 : 1 ≤ s₀.re := by rw [hs₀re, hncast]; linarith
    have h2' : s₀.re ≤ 2 := by rw [hs₀re, hncast]; linarith
    have hs₀im : s₀.im = s.im := by simp [hs₀]
    have hsum : s = s₀ + n := by simp [hs₀]
    have hψ : digamma s = digamma s₀ + ∑ k ∈ Finset.range n, (s₀ + k)⁻¹ := by
      rw [hsum]; exact digamma_add_nat s₀ (by linarith) n
    have hψ₀ : ‖digamma s₀‖ ≤ C₀ * Real.log (2 + ‖s‖) := by
      have h := (H s₀ ((min_le_right δ 1).trans h1) h2').1
      rw [hs₀im] at h
      exact h.trans (mul_le_mul_of_nonneg_left him hC₀.le)
    have h2flR : (2 : ℝ) ≤ (⌊s.re⌋₊ : ℝ) := by exact_mod_cast h2fl
    have hn1 : (1 : ℝ) ≤ n := by rw [hncast]; linarith
    have hnle : (n : ℝ) ≤ 2 + ‖s‖ := by
      have := Complex.re_le_norm s; rw [hncast]; linarith
    have hharm : (harmonic n : ℝ) ≤ 1 + Real.log (2 + ‖s‖) :=
      (harmonic_le_one_add_log n).trans (by
        have := Real.log_le_log (by linarith) hnle; linarith)
    rw [hψ]
    calc ‖digamma s₀ + ∑ k ∈ Finset.range n, (s₀ + (k : ℂ))⁻¹‖
        ≤ ‖digamma s₀‖ + ‖∑ k ∈ Finset.range n, (s₀ + (k : ℂ))⁻¹‖ := norm_add_le _ _
      _ ≤ C₀ * Real.log (2 + ‖s‖) + (1 + Real.log (2 + ‖s‖)) :=
          add_le_add hψ₀ ((norm_sum_inv_le_harmonic s₀ h1 n).trans hharm)
      _ ≤ (C₀ + 3) * Real.log (2 + ‖s‖) := by nlinarith

theorem logDeriv_GammaComplex (s : ℂ) (hs : 0 < s.re) :
    logDeriv Complex.Gammaℂ s = -Complex.log (2 * (Real.pi : ℂ)) + digamma s := by
  have hc : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero two_ne_zero; exact_mod_cast Real.pi_ne_zero
  have hΓ : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hΓd : DifferentiableAt ℂ Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m heq => ?_
    have := congrArg Complex.re heq; simp at this; have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hE : HasDerivAt (fun x : ℂ => (2 * (Real.pi : ℂ)) ^ (-x)) ((2 * (Real.pi : ℂ)) ^ (-s) * Complex.log (2 * (Real.pi : ℂ)) * (-1)) s :=
    (hasDerivAt_id s).neg.const_cpow (Or.inl hc)
  have hEne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hc h.1
  have hF : DifferentiableAt ℂ (fun x : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-x)) s := (hE.differentiableAt.const_mul 2)
  rw [show Complex.Gammaℂ = fun x => (2 * (2 * (Real.pi : ℂ)) ^ (-x)) * Gamma x from rfl,
    logDeriv_mul (f := fun x : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-x)) (g := Gamma) s (mul_ne_zero two_ne_zero hEne) hΓ hF hΓd,
    logDeriv_const_mul (f := fun x : ℂ => (2 * (Real.pi : ℂ)) ^ (-x)) s 2 two_ne_zero, logDeriv_apply, hE.deriv]
  show (2 * (Real.pi : ℂ)) ^ (-s) * Complex.log (2 * (Real.pi : ℂ)) * -1 / (2 * (Real.pi : ℂ)) ^ (-s) + logDeriv Gamma s = _
  rw [show logDeriv Gamma = digamma from rfl]
  field_simp

theorem logDeriv_GammaReal (s : ℂ) (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Complex.log (Real.pi : ℂ)) / 2 + digamma (s / 2) / 2 := by
  have hc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hΓ : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2
  have hΓd : DifferentiableAt ℂ Gamma (s / 2) := by
    refine Complex.differentiableAt_Gamma _ fun m heq => ?_
    have := congrArg Complex.re heq; simp at this; have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hE : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) ^ (-x / 2)) ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s :=
    ((hasDerivAt_id s).neg.div_const 2).const_cpow (Or.inl hc)
  have hEne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hc h.1
  have hg : HasDerivAt (fun x : ℂ => x / 2) (1 / 2) s := (hasDerivAt_id s).div_const 2
  have hG : DifferentiableAt ℂ (fun x : ℂ => Gamma (x / 2)) s := hΓd.comp s hg.differentiableAt
  rw [show Complex.Gammaℝ = fun x => (Real.pi : ℂ) ^ (-x / 2) * Gamma (x / 2) from rfl,
    logDeriv_mul (f := fun x : ℂ => (Real.pi : ℂ) ^ (-x / 2)) (g := fun x : ℂ => Gamma (x / 2)) s hEne hΓ hE.differentiableAt hG, logDeriv_apply, hE.deriv,
    show (fun x : ℂ => Gamma (x / 2)) = Gamma ∘ (fun x : ℂ => x / 2) from rfl,
    logDeriv_comp (f := Gamma) (g := fun x : ℂ => x / 2) hΓd hg.differentiableAt, hg.deriv, show logDeriv Gamma = digamma from rfl]
  field_simp

theorem norm_log_ofReal_le (x : ℝ) (hx : 1 ≤ x) : ‖Complex.log (x : ℂ)‖ ≤ x := by
  rw [← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hx)]
  exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)

theorem main (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℂ s‖ ≤ C * Real.log (2 + ‖s‖) := by
  obtain ⟨C₁, hC₁, H₁⟩ := digamma_halfplane δ hδ
  obtain ⟨C₂, hC₂, H₂⟩ := digamma_halfplane (δ / 2) (by linarith)
  refine ⟨C₁ + C₂ + 18, by linarith, fun s hs => ⟨?_, ?_, ?_⟩⟩
  all_goals have hn0 : 0 ≤ ‖s‖ := norm_nonneg s
  all_goals have hL0 := log_two_add_nonneg ‖s‖ hn0
  all_goals have hL1 := one_le_two_mul_log_two_add ‖s‖ hn0
  all_goals have hspos : 0 < s.re := lt_of_lt_of_le hδ hs
  all_goals have hC₁L : 0 ≤ C₁ * Real.log (2 + ‖s‖) := mul_nonneg hC₁.le hL0
  all_goals have hC₂L : 0 ≤ C₂ * Real.log (2 + ‖s‖) := mul_nonneg hC₂.le hL0
  · have := H₁ s hs; linarith
  · rw [logDeriv_GammaReal s hspos]
    have hψ : ‖digamma (s / 2)‖ ≤ C₂ * Real.log (2 + ‖s‖) := by
      have h := H₂ (s / 2) (by simp; linarith)
      refine h.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hC₂.le)
      rw [norm_div, Complex.norm_two]; linarith
    have hpi : ‖Complex.log (Real.pi : ℂ)‖ ≤ 4 :=
      (norm_log_ofReal_le Real.pi (by linarith [Real.pi_gt_three])).trans Real.pi_le_four
    calc ‖-Complex.log (Real.pi : ℂ) / 2 + digamma (s / 2) / 2‖
        ≤ ‖-Complex.log (Real.pi : ℂ) / 2‖ + ‖digamma (s / 2) / 2‖ := norm_add_le _ _
      _ = ‖Complex.log (Real.pi : ℂ)‖ / 2 + ‖digamma (s / 2)‖ / 2 := by simp [norm_neg]
      _ ≤ 4 / 2 + C₂ * Real.log (2 + ‖s‖) / 2 := by gcongr
      _ ≤ (C₁ + C₂ + 18) * Real.log (2 + ‖s‖) := by linarith
  · rw [logDeriv_GammaComplex s hspos]
    have hψ := H₁ s hs
    have h2pi : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ 8 := by
      have : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      refine (norm_log_ofReal_le (2 * Real.pi) (by linarith [Real.pi_gt_three])).trans ?_
      linarith [Real.pi_le_four]
    calc ‖-Complex.log (2 * (Real.pi : ℂ)) + digamma s‖
        ≤ ‖-Complex.log (2 * (Real.pi : ℂ))‖ + ‖digamma s‖ := norm_add_le _ _
      _ = ‖Complex.log (2 * (Real.pi : ℂ))‖ + ‖digamma s‖ := by rw [norm_neg]
      _ ≤ 8 + C₁ * Real.log (2 + ‖s‖) := add_le_add h2pi hψ
      _ ≤ (C₁ + C₂ + 18) * Real.log (2 + ‖s‖) := by linarith

end Ws31.Digamma

theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℂ s‖ ≤ C * Real.log (2 + ‖s‖) :=
  Ws31.Digamma.main δ hδ

end S_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
end P2MW
export P2MW.S_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re (solution)
