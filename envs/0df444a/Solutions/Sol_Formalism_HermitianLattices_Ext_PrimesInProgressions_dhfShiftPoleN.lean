-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhfShiftPoleN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:45:29.715795+00:00
-- url     : https://prove2.me/submissions/b783a38d-2425-43ff-b525-d6608733d1c0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqFA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
private theorem norm_inv_pow_sub_inv_pow_le (a b : ℂ) (η δ : ℝ) (hη : 0 < η) (ha : η ≤ ‖a‖) (hb : η ≤ ‖b‖)
    (hab : ‖b - a‖ ≤ δ) (n : ℕ) : ‖1 / a ^ n - 1 / b ^ n‖ ≤ n * δ / η ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      linarith
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, norm_zero] at hb
      linarith
    have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hab
    have key : 1 / a ^ (n + 1) - 1 / b ^ (n + 1) =
        (1 / a) * (1 / a ^ n - 1 / b ^ n) + (1 / b ^ n) * ((b - a) / (a * b)) := by
      field_simp
      ring
    rw [key]
    have h1 : ‖1 / a‖ ≤ 1 / η := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hη ha
    have h2 : ‖1 / b ^ n‖ ≤ 1 / η ^ n := by
      rw [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le (pow_pos hη n) (pow_le_pow_left₀ hη.le hb n)
    have h3 : ‖(b - a) / (a * b)‖ ≤ δ / (η * η) := by
      rw [norm_div, norm_mul]
      exact div_le_div₀ hδ hab (mul_pos hη hη) (mul_le_mul ha hb hη.le (norm_nonneg _))
    calc _ ≤ ‖1 / a‖ * ‖1 / a ^ n - 1 / b ^ n‖ + ‖1 / b ^ n‖ * ‖(b - a) / (a * b)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 / η * (n * δ / η ^ (n + 1)) + 1 / η ^ n * (δ / (η * η)) := by gcongr
      _ = _ := by
        push_cast
        field_simp
        ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : β₁ < 1) (k : ℕ) (c : Prop) [Decidable c]
    (hc : ¬ c → 1 / 8 ≤ |γ|) (s : ℂ) (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) :
    ‖1 / (s - 1) ^ (k + 1) - (if c then 1 / (s - β₁) ^ (k + 1) else 0)‖ ≤
      ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
  have hre1 : (s - 1).re = η := by
    rw [hs]
    simp
  have hre2 : (s - (β₁ : ℂ)).re = 1 + η - β₁ := by
    rw [hs]
    simp
  have him : (s - 1).im = γ := by
    rw [hs]
    simp
  have hsa : η ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [hre1, abs_of_pos hη] at this
    exact this
  have hsb : η ≤ ‖s - (β₁ : ℂ)‖ := by
    have := Complex.re_le_norm (s - (β₁ : ℂ))
    rw [hre2] at this
    linarith
  have hd : ‖(s - (β₁ : ℂ)) - (s - 1)‖ ≤ 1 - β₁ := by
    have e : (s - (β₁ : ℂ)) - (s - 1) = ((1 - β₁ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h8 : (0 : ℝ) ≤ 8 ^ (k + 1) := by positivity
  have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
    apply div_nonneg
    · apply mul_nonneg
      · positivity
      · linarith
    · positivity
  split_ifs with h
  · have := norm_inv_pow_sub_inv_pow_le (s - 1) (s - β₁) η (1 - β₁) hη hsa hsb hd (k + 1)
    push_cast at this
    linarith
  · have hγ : 1 / 8 ≤ |γ| := hc h
    have hs1 : 1 / 8 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [him] at this
      linarith
    rw [sub_zero, norm_div, norm_one, norm_pow]
    have hb : 1 / ‖s - 1‖ ^ (k + 1) ≤ 8 ^ (k + 1) := by
      rw [div_le_iff₀ (by positivity)]
      calc (1 : ℝ) = 8 ^ (k + 1) * (1 / 8) ^ (k + 1) := by
            rw [← mul_pow]
            norm_num
        _ ≤ 8 ^ (k + 1) * ‖s - 1‖ ^ (k + 1) := by gcongr
    linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
