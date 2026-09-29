-- Prove2me | solution 1 for EulerProduct.differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2fd2c27b-03ac-5d24-bbbf-b4b88b00e928

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div

set_option autoImplicit false

open Complex

namespace R1EulerLogDeriv

lemma norm_coeff_le (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ ≤ 1) (z : ℂ) :
    ‖c * (N : ℂ) ^ (-z)‖ ≤ (N : ℝ) ^ (-z.re) := by
  rw [norm_mul, norm_natCast_cpow_of_pos (by omega), neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hc

lemma rpow_neg_le_rpow_neg (N : ℕ) (hN : 2 ≤ N) {σ σ' : ℝ} (h : σ' ≤ σ) :
    (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ') := by
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (by omega : 1 ≤ N)
  · linarith

lemma rpow_neg_le_half (N : ℕ) (hN : 2 ≤ N) (σ : ℝ) (hσ : 1 ≤ σ) : (N : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(1 : ℝ)) := rpow_neg_le_rpow_neg N hN hσ
  have h2 : (N : ℝ) ^ (-(1 : ℝ)) = 1 / N := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_one, one_div]
  have h3 : (1 : ℝ) / N ≤ 1 / 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    exact one_div_le_one_div_of_le (by norm_num) this
  linarith [h1, h2.le, h2.ge, h3]

theorem main {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ))
    (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹) s ∧
    (∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 ∧
    HasSum (fun i => (Real.log (N i) : ℂ) * (c i * ((N i : ℕ) : ℂ) ^ (-s)) /
        (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))
      (-(deriv (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹) s /
          ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹)) := by
  set a : ι → ℂ → ℂ := fun i z => c i * ((N i : ℕ) : ℂ) ^ (-z) with ha
  set g : ι → ℂ → ℂ := fun i z => -log (1 - a i z) with hg
  set G : ℂ → ℂ := fun z => ∑' i, g i z with hG
  set E : ℂ → ℂ := fun z => ∏' i, (1 - a i z)⁻¹ with hE
  set σ₁ : ℝ := (1 + s.re) / 2 with hσ₁
  have hσ₁1 : 1 < σ₁ := by rw [hσ₁]; linarith
  have hσ₁s : σ₁ < s.re := by rw [hσ₁]; linarith
  set U : Set ℂ := {z : ℂ | σ₁ < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hσ₁s
  have hN0 : ∀ i, (N i : ℂ) ≠ 0 := fun i => Nat.cast_ne_zero.mpr (by have := hN i; omega)

  have hnorm_a : ∀ i, ∀ z ∈ U, ‖a i z‖ ≤ ((N i : ℕ) : ℝ) ^ (-σ₁) := by
    intro i z hz
    have hz' : σ₁ ≤ z.re := le_of_lt hz
    exact (norm_coeff_le (N i) (hN i) (c i) (hc i) z).trans (rpow_neg_le_rpow_neg (N i) (hN i) hz')
  have hhalf : ∀ i, ∀ z ∈ U, ‖a i z‖ ≤ 1 / 2 := fun i z hz =>
    (hnorm_a i z hz).trans (rpow_neg_le_half (N i) (hN i) σ₁ hσ₁1.le)
  have hne : ∀ i, ∀ z ∈ U, 1 - a i z ≠ 0 := by
    intro i z hz h0
    have : a i z = 1 := (sub_eq_zero.mp h0).symm
    have h1 := hhalf i z hz
    rw [this, norm_one] at h1
    norm_num at h1
  have hslit : ∀ i, ∀ z ∈ U, 1 - a i z ∈ slitPlane := by
    intro i z hz
    rw [sub_eq_add_neg]
    apply mem_slitPlane_of_norm_lt_one
    rw [norm_neg]
    linarith [hhalf i z hz]

  have hda : ∀ i z, HasDerivAt (a i) (-(Real.log (N i) : ℂ) * a i z) z := by
    intro i z
    have h1 : HasDerivAt (fun z : ℂ => -z) (-1) z := (hasDerivAt_id z).neg
    have h2 : HasDerivAt (fun z : ℂ => ((N i : ℕ) : ℂ) ^ (-z))
        (((N i : ℕ) : ℂ) ^ (-z) * log ((N i : ℕ) : ℂ) * (-1)) z :=
      h1.const_cpow (Or.inl (hN0 i))
    have h3 := h2.const_mul (c i)
    have hval : c i * (((N i : ℕ) : ℂ) ^ (-z) * log ((N i : ℕ) : ℂ) * (-1))
        = -(Real.log (N i) : ℂ) * a i z := by
      rw [natCast_log]
      simp only [ha]
      ring
    rw [hval] at h3
    exact h3
  have hdg : ∀ i, ∀ z ∈ U,
      HasDerivAt (g i) (-((Real.log (N i) : ℂ) * a i z / (1 - a i z))) z := by
    intro i z hz
    have h1 : HasDerivAt (fun w => 1 - a i w) (-(-(Real.log (N i) : ℂ) * a i z)) z :=
      (hda i z).const_sub 1
    have h2 := h1.clog (hslit i z hz)
    have h3 := h2.neg
    have hval : -(-(-(Real.log (N i) : ℂ) * a i z) / (1 - a i z))
        = -((Real.log (N i) : ℂ) * a i z / (1 - a i z)) := by ring
    rw [hval] at h3
    exact h3
  have hgdiff : ∀ i, DifferentiableOn ℂ (g i) U :=
    fun i z hz => (hdg i z hz).differentiableAt.differentiableWithinAt
  have hgle : ∀ i, ∀ z ∈ U, ‖g i z‖ ≤ 3 / 2 * ((N i : ℕ) : ℝ) ^ (-σ₁) := by
    intro i z hz
    have h1 : ‖log (1 + -a i z)‖ ≤ 3 / 2 * ‖-a i z‖ :=
      norm_log_one_add_half_le_self (by rw [norm_neg]; exact hhalf i z hz)
    rw [← sub_eq_add_neg, norm_neg] at h1
    calc ‖g i z‖ = ‖log (1 - a i z)‖ := by simp [hg]
      _ ≤ 3 / 2 * ‖a i z‖ := h1
      _ ≤ 3 / 2 * ((N i : ℕ) : ℝ) ^ (-σ₁) := by gcongr; exact hnorm_a i z hz
  have hu : Summable fun i => 3 / 2 * ((N i : ℕ) : ℝ) ^ (-σ₁) := (hsum σ₁ hσ₁1).mul_left _

  have hGsum : HasSum (fun i => deriv (g i) s) (deriv G s) :=
    hasSum_deriv_of_summable_norm hu hgdiff hUo hgle hsU
  have hGdiff : DifferentiableOn ℂ G U := differentiableOn_tsum_of_summable_norm hu hgdiff hUo hgle

  have hEG : ∀ z ∈ U, E z = exp (G z) := by
    intro z hz
    have hsz : Summable fun i => g i z :=
      Summable.of_norm_bounded hu (fun i => hgle i z hz)
    have H := hsz.hasSum.cexp.tprod_eq
    have hcongr : (cexp ∘ fun i => g i z) = fun i => (1 - a i z)⁻¹ := by
      funext i
      simp only [Function.comp_apply, hg, exp_neg, exp_log (hne i z hz)]
    rw [hcongr] at H
    exact H
  have hEev : E =ᶠ[nhds s] fun z => exp (G z) :=
    Filter.eventuallyEq_of_mem (hUo.mem_nhds hsU) hEG
  have hGs : HasDerivAt G (deriv G s) s := (hGdiff.differentiableAt (hUo.mem_nhds hsU)).hasDerivAt
  have hexpG : HasDerivAt (fun z => exp (G z)) (exp (G s) * deriv G s) s := hGs.cexp
  have hEderiv : HasDerivAt E (exp (G s) * deriv G s) s := hexpG.congr_of_eventuallyEq hEev
  have hEs : E s = exp (G s) := hEG s hsU
  refine ⟨hEderiv.differentiableAt, ?_, ?_⟩
  · show E s ≠ 0
    rw [hEs]
    exact exp_ne_zero _
  · have h1 : -(deriv E s / E s) = -deriv G s := by
      rw [hEderiv.deriv, hEs, mul_div_cancel_left₀ _ (exp_ne_zero _)]
    have h2 : ∀ i, deriv (g i) s = -((Real.log (N i) : ℂ) * a i s / (1 - a i s)) :=
      fun i => (hdg i s hsU).deriv
    have h3 := hGsum.neg
    have h4 : (fun i => -deriv (g i) s) = fun i => (Real.log (N i) : ℂ) * a i s / (1 - a i s) := by
      funext i
      rw [h2 i, neg_neg]
    rw [h4] at h3
    show HasSum (fun i => (Real.log (N i) : ℂ) * a i s / (1 - a i s)) (-(deriv E s / E s))
    rw [h1]
    exact h3

end R1EulerLogDeriv

theorem solution
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ))
    (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹) s ∧
    (∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 ∧
    HasSum (fun i => (Real.log (N i) : ℂ) * (c i * ((N i : ℕ) : ℂ) ^ (-s)) /
        (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))
      (-(deriv (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹) s /
          ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹)) :=
  R1EulerLogDeriv.main N hN c hc hsum s hs

end S_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
end P2MW
export P2MW.S_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div (solution)
