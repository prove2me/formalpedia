-- Prove2me | solution 1 for FaulhuberTFA.ambiguity_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:32:57.81829+00:00
-- url     : https://prove2.me/submissions/cd375a70-ca55-4c95-99f2-79b73906417e

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
theorem solution (x ω : Rd 1) :
    ambiguity (gauss0 1) x ω = (Real.exp (-(Real.pi / 2) * (‖x‖ ^ 2 + ‖ω‖ ^ 2)) : ℂ) :=
  ex_core x ω
