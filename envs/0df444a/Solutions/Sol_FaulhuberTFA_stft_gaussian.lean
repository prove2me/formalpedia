-- Prove2me | solution 1 for FaulhuberTFA.stft_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:32:54.626672+00:00
-- url     : https://prove2.me/submissions/f390fe99-a2f6-4a94-8340-b290038e28e8

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

set_option autoImplicit false

namespace FaulhuberTFA

lemma ex_norm_id {d : ℕ} (x s : Rd d) :
    ‖s + (1 / 2 : ℝ) • x‖ ^ 2 + ‖s - (1 / 2 : ℝ) • x‖ ^ 2 = 2 * ‖s‖ ^ 2 + ‖x‖ ^ 2 / 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, inner_smul_right]
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  ring

lemma ex_pt {d : ℕ} (x ω s : Rd d) :
    gauss0 d (s + (1 / 2 : ℝ) • x) * starRingEnd ℂ (gauss0 d (s - (1 / 2 : ℝ) • x)) *
        ePhase (-⟪ω, s⟫_ℝ) =
      (((2 : ℝ) ^ ((d : ℝ) / 4)) ^ 2 * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2) : ℝ) *
        cexp (-(2 * (Real.pi : ℂ)) * ((‖s‖ : ℝ) : ℂ) ^ 2 +
          (-2 * (Real.pi : ℂ) * I) * ((⟪ω, s⟫_ℝ : ℝ) : ℂ)) := by
  simp only [gauss0, ePhase, Complex.conj_ofReal]
  push_cast
  have h := ex_norm_id x s
  have h' : ((‖s + (1 / 2 : ℝ) • x‖ : ℂ)) ^ 2 + ((‖s - (1 / 2 : ℝ) • x‖ : ℂ)) ^ 2
      = 2 * (‖s‖ : ℂ) ^ 2 + (‖x‖ : ℂ) ^ 2 / 2 := by exact_mod_cast h
  have e1 : ∀ a b c : ℂ, ∀ K : ℂ, K * cexp a * (K * cexp b) * cexp c = K ^ 2 * cexp (a + b + c) := by
    intro a b c K; rw [Complex.exp_add, Complex.exp_add]; ring
  rw [e1]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 2
  linear_combination (-(Real.pi : ℂ)) * h'

lemma ex_core {d : ℕ} (x ω : Rd d) :
    ∫ s, gauss0 d (s + (1 / 2 : ℝ) • x) * starRingEnd ℂ (gauss0 d (s - (1 / 2 : ℝ) • x)) *
        ePhase (-⟪ω, s⟫_ℝ) =
      (Real.exp (-(Real.pi / 2) * (‖x‖ ^ 2 + ‖ω‖ ^ 2)) : ℂ) := by
  simp_rw [ex_pt x ω]
  rw [integral_const_mul]
  have hb : 0 < (2 * (Real.pi : ℂ)).re := by simp [Real.pi_pos]
  have := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb (-2 * (Real.pi : ℂ) * I) ω
  simp only [finrank_euclideanSpace_fin] at this
  rw [this]
  have hK : ((2:ℝ) ^ ((d:ℝ) / 4)) ^ 2 * (1 / 2 : ℝ) ^ ((d:ℝ) / 2) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, Real.inv_rpow (by norm_num),
      show (d:ℝ) / 4 * ((2:ℕ):ℝ) = (d:ℝ) / 2 by push_cast; ring]
    exact mul_inv_cancel₀ (by positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (Real.pi : ℂ) / (2 * Real.pi) = ((1 / 2 : ℝ) : ℂ) := by
    field_simp; push_cast; ring
  have h2 : ((d:ℂ) / 2) = (((d:ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have h3 : (-2 * (Real.pi : ℂ) * I) ^ 2 * ((‖ω‖ : ℝ) : ℂ) ^ 2 / (4 * (2 * Real.pi))
      = ((-(Real.pi / 2) * ‖ω‖ ^ 2 : ℝ) : ℂ) := by
    rw [show (-2 * (Real.pi : ℂ) * I) ^ 2 = -(4 * (Real.pi : ℂ) ^ 2) by
      ring_nf; rw [I_sq]; ring]
    field_simp; push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (by norm_num), h3, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul]
  congr 1
  rw [show -(Real.pi / 2) * (‖x‖ ^ 2 + ‖ω‖ ^ 2) = -(Real.pi / 2) * ‖x‖ ^ 2 + -(Real.pi / 2) * ‖ω‖ ^ 2
    by ring, Real.exp_add]
  linear_combination (Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2) * Real.exp (-(Real.pi / 2) * ‖ω‖ ^ 2)) * hK

end FaulhuberTFA

open FaulhuberTFA in
theorem solution {d : ℕ} (x ω : Rd d) :
    stft (gauss0 d) (gauss0 d) x ω =
      Complex.exp (-(Real.pi * Complex.I * (⟪x, ω⟫_ℝ : ℂ))) *
        (Real.exp (-(Real.pi / 2) * (‖x‖ ^ 2 + ‖ω‖ ^ 2)) : ℂ) := by
  unfold stft
  rw [← integral_add_right_eq_self _ ((1 / 2 : ℝ) • x)]
  have hpt : ∀ s : Rd d, gauss0 d (s + (1 / 2 : ℝ) • x) *
      starRingEnd ℂ (gauss0 d (s + (1 / 2 : ℝ) • x - x)) * ePhase (-⟪ω, s + (1 / 2 : ℝ) • x⟫_ℝ) =
      gauss0 d (s + (1 / 2 : ℝ) • x) * starRingEnd ℂ (gauss0 d (s - (1 / 2 : ℝ) • x)) *
        ePhase (-⟪ω, s⟫_ℝ) * Complex.exp (-(Real.pi * Complex.I * (⟪x, ω⟫_ℝ : ℂ))) := by
    intro s
    have e : s + (1 / 2 : ℝ) • x - x = s - (1 / 2 : ℝ) • x := by
      rw [sub_eq_sub_iff_add_eq_add, add_assoc, ← add_smul]; norm_num
    rw [e, mul_assoc _ (ePhase _), ePhase, ePhase, ← Complex.exp_add, inner_add_right,
      inner_smul_right, real_inner_comm ω x]
    congr 3
    push_cast; ring
  simp_rw [hpt]
  rw [integral_mul_const, ex_core, mul_comm]
