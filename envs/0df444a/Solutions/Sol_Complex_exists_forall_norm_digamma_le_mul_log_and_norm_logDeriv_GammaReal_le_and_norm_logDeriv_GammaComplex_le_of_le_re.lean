-- Prove2me | solution 1 for Complex.exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/58dbffe9-a14a-51f0-ace3-07a3aa7eb979

import Mathlib
import Theorems.Thm_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re

set_option autoImplicit false

noncomputable section

open Complex

namespace DigammaStrip

theorem ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ m : ℕ, s ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  rw [neg_re, natCast_re] at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem hasDerivAt_const_cpow_linear {a : ℂ} (ha : a ≠ 0) (c s : ℂ) :
    HasDerivAt (fun z : ℂ => a ^ (c * z)) (a ^ (c * s) * (Complex.log a * c)) s := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.log a * (c * z)) (Complex.log a * c) s := by
    have := ((hasDerivAt_id s).const_mul c).const_mul (Complex.log a)
    simpa using this
  have e : (fun z : ℂ => a ^ (c * z)) = fun z => Complex.exp (Complex.log a * (c * z)) := by
    funext z; rw [cpow_def_of_ne_zero ha]
  rw [e, cpow_def_of_ne_zero ha]
  exact h1.cexp

theorem const_cpow_ne_zero {a : ℂ} (ha : a ≠ 0) (z : ℂ) : a ^ z ≠ 0 := by
  rw [cpow_def_of_ne_zero ha]; exact Complex.exp_ne_zero _

theorem logDeriv_const_cpow_linear {a : ℂ} (ha : a ≠ 0) (c s : ℂ) :
    logDeriv (fun z : ℂ => a ^ (c * z)) s = Complex.log a * c := by
  rw [logDeriv_apply, (hasDerivAt_const_cpow_linear ha c s).deriv, mul_div_cancel_left₀ _ (const_cpow_ne_zero ha _)]

theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -(Complex.log (Real.pi : ℂ)) / 2 + digamma (s / 2) / 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hs2 : 0 < (s / 2).re := by rw [div_ofNat_re]; positivity
  have e : Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ ((-(1 / 2 : ℂ)) * z) * (Gamma ∘ fun z : ℂ => z / 2) z := by
    funext z
    rw [Gammaℝ_def, Function.comp_apply]
    congr 2
    ring
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := DifferentiableAt.div_const differentiableAt_id 2
  have hG : DifferentiableAt ℂ Gamma ((fun z : ℂ => z / 2) s) := differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hs2)
  have hGc : DifferentiableAt ℂ (Gamma ∘ fun z : ℂ => z / 2) s := hG.comp s hdiv
  rw [e, logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ ((-(1 / 2 : ℂ)) * z)) (g := Gamma ∘ fun z : ℂ => z / 2) s
    (const_cpow_ne_zero hπ _) (Gamma_ne_zero_of_re_pos hs2) (hasDerivAt_const_cpow_linear hπ _ s).differentiableAt hGc,
    logDeriv_const_cpow_linear hπ, logDeriv_comp (f := Gamma) (g := fun z : ℂ => z / 2) (x := s) hG hdiv]
  have hd : deriv (fun z : ℂ => z / 2) s = 1 / 2 := by
    rw [deriv_div_const, deriv_id'']
  rw [hd, digamma_def]
  ring

theorem logDeriv_Gammaℂ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℂ s = -Complex.log (2 * Real.pi : ℂ) + digamma s := by
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  have e : Gammaℂ = fun z : ℂ => 2 * ((2 * Real.pi : ℂ) ^ ((-1 : ℂ) * z) * Gamma z) := by
    funext z
    rw [Gammaℂ_def, neg_one_mul, mul_assoc]
  rw [e, logDeriv_const_mul (f := fun z : ℂ => (2 * Real.pi : ℂ) ^ ((-1 : ℂ) * z) * Gamma z) s 2 two_ne_zero,
    logDeriv_mul (f := fun z : ℂ => (2 * Real.pi : ℂ) ^ ((-1 : ℂ) * z)) (g := Gamma) s (const_cpow_ne_zero h2π _)
    (Gamma_ne_zero_of_re_pos hs) (hasDerivAt_const_cpow_linear h2π _ s).differentiableAt
    (differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hs)),
    logDeriv_const_cpow_linear h2π, digamma_def]
  ring

theorem norm_log_pi : ‖Complex.log (Real.pi : ℂ)‖ = Real.log Real.pi := by
  rw [← ofReal_log Real.pi_pos.le, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]

theorem norm_log_two_pi : ‖Complex.log (2 * Real.pi : ℂ)‖ = Real.log (2 * Real.pi) := by
  have : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← ofReal_log (by positivity), norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]

end DigammaStrip

open DigammaStrip in
theorem solution
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) ∧
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C * Real.log (2 + |s.im|) ∧
      ‖logDeriv Complex.Gammaℂ s‖ ≤ C * Real.log (2 + |s.im|) := by
  obtain ⟨C₁, hC₁, h₁⟩ := Complex.exists_forall_norm_digamma_le_mul_log_of_le_re δ hδ
  obtain ⟨C₂, hC₂, h₂⟩ := Complex.exists_forall_norm_digamma_le_mul_log_of_le_re (δ / 2) (by positivity)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl2π : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  set C : ℝ := C₁ + C₂ + (Real.log Real.pi + Real.log (2 * Real.pi)) / Real.log 2 + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  refine ⟨C, hCpos, fun s hδs hs2 => ?_⟩
  have hs : 0 < s.re := lt_of_lt_of_le hδ hδs
  set L : ℝ := Real.log (2 + |s.im|) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hL0 : 0 < L := lt_of_lt_of_le hl2 hL2
  have hψ : ‖digamma s‖ ≤ C₁ * L := h₁ s hδs hs2
  have hψ2 : ‖digamma (s / 2)‖ ≤ C₂ * L := by
    have hre : (s / 2).re = s.re / 2 := div_ofNat_re s 2
    have him : (s / 2).im = s.im / 2 := div_ofNat_im s 2
    have := h₂ (s / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [him] at this
    refine this.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hC₂.le)
    rw [abs_div, abs_two]
    linarith [abs_nonneg s.im]

  have habs : ∀ {a : ℝ}, 0 ≤ a → a ≤ a / Real.log 2 * L := fun {a} ha => by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hL2 ha
  have hC₁le : C₁ ≤ C := by
    rw [hC]
    have : 0 ≤ (Real.log Real.pi + Real.log (2 * Real.pi)) / Real.log 2 := by positivity
    linarith
  refine ⟨hψ.trans (mul_le_mul_of_nonneg_right hC₁le hL0.le), ?_, ?_⟩
  · rw [logDeriv_Gammaℝ hs]
    calc ‖-Complex.log (Real.pi : ℂ) / 2 + digamma (s / 2) / 2‖
        ≤ ‖-Complex.log (Real.pi : ℂ) / 2‖ + ‖digamma (s / 2) / 2‖ := norm_add_le _ _
      _ = Real.log Real.pi / 2 + ‖digamma (s / 2)‖ / 2 := by
          rw [norm_div, norm_neg, norm_log_pi, norm_div]; norm_num
      _ ≤ (Real.log Real.pi / Real.log 2 * L) / 2 + (C₂ * L) / 2 := by gcongr; exact habs hlπ
      _ ≤ C * L := by
          have e1 : C * L = C₁ * L + C₂ * L + Real.log Real.pi / Real.log 2 * L + Real.log (2 * Real.pi) / Real.log 2 * L + L := by
            rw [hC]; ring
          have : 0 ≤ Real.log (2 * Real.pi) / Real.log 2 * L := by positivity
          have : 0 ≤ C₁ * L := by positivity
          have : 0 ≤ C₂ * L := by positivity
          have : 0 ≤ Real.log Real.pi / Real.log 2 * L := by positivity
          linarith
  · rw [logDeriv_Gammaℂ hs]
    calc ‖-Complex.log (2 * Real.pi : ℂ) + digamma s‖
        ≤ ‖-Complex.log (2 * Real.pi : ℂ)‖ + ‖digamma s‖ := norm_add_le _ _
      _ = Real.log (2 * Real.pi) + ‖digamma s‖ := by rw [norm_neg, norm_log_two_pi]
      _ ≤ Real.log (2 * Real.pi) / Real.log 2 * L + C₁ * L := add_le_add (habs hl2π) hψ
      _ ≤ C * L := by
          have e1 : C * L = C₁ * L + C₂ * L + Real.log Real.pi / Real.log 2 * L + Real.log (2 * Real.pi) / Real.log 2 * L + L := by
            rw [hC]; ring
          have : 0 ≤ Real.log Real.pi / Real.log 2 * L := by positivity
          have : 0 ≤ C₂ * L := by positivity
          linarith

end

end S_Complex_exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
end P2MW
export P2MW.S_Complex_exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re (solution)
