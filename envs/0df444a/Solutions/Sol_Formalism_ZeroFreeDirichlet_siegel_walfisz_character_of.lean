-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.siegel_walfisz_character_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:58:56.873825+00:00
-- url     : https://prove2.me/submissions/353c81cd-4d59-4714-aef0-ca959cebcf99

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zero_free_region_mono
import Theorems.Thm_Formalism_ZeroFreeDirichlet_half_le_of_real_in_region
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exists_exceptional_zero_set
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_trivial_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exceptional_zero_term_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_bounded_of_exp_sqrt_lt_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : SiegelWalfiszOf := by
  intro hP hZ hE A hA
  obtain ⟨cZ, hcZ, hZ'⟩ := hZ
  set c₁ : ℝ := min cZ (1 / 20) with hc₁
  have hc₁0 : 0 < c₁ := lt_min hcZ (by norm_num)
  have hc₁20 : c₁ ≤ 1 / 20 := min_le_right _ _
  have hc₁Z : c₁ ≤ cZ := min_le_left _ _
  obtain ⟨c, C, hc, hPC⟩ := hP c₁ hc₁0 hc₁20
  obtain ⟨cE, hcE, hEB⟩ := hE (1 / (2 * A)) (by positivity)
  obtain ⟨U, hU0, hU⟩ := bounded_of_exp_sqrt_lt_pow A c hA hc
  set cf : ℝ := min c cE with hcf
  have hcf0 : 0 < cf := lt_min hc hcE
  have hK0 : 0 ≤ (U + 1) * Real.exp (cf * Real.sqrt U) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  refine ⟨cf, (max C 0 + 2) + (U + 1) * Real.exp (cf * Real.sqrt U), hcf0, ?_⟩
  intro q _ χ x hx hqL
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hq1 : (1:ℝ) ≤ q := by
    have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast h1
  have hM0 : 0 ≤ (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
    mul_nonneg (mul_nonneg (by linarith [le_max_right C 0]) hx0) (Real.exp_pos _).le
  have hK : 0 ≤ (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
    mul_nonneg (mul_nonneg hK0 hx0) (Real.exp_pos _).le
  have hfin : ((max C 0 + 2) + (U + 1) * Real.exp (cf * Real.sqrt U)) * x *
      Real.exp (-cf * Real.sqrt (Real.log x)) =
      (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x)) +
      (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by ring
  rw [hfin]
  by_cases hsmall : Real.exp (c * Real.sqrt (Real.log x)) < Real.log x ^ A
  · have hLU : Real.log x ≤ U := hU (Real.log x) hlx hsmall
    have htriv := chebyshev_character_trivial_bound χ x hx1
    have hsqU : Real.sqrt (Real.log x) ≤ Real.sqrt U := Real.sqrt_le_sqrt hLU
    have he : 1 ≤ Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hxU : 0 ≤ x * (U + 1) := mul_nonneg hx0 (by linarith)
    have s1 : x * (Real.log x + 1) ≤ x * (U + 1) := mul_le_mul_of_nonneg_left (by linarith) hx0
    have s2 : x * (U + 1) ≤ x * (U + 1) * (Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x))) :=
      le_mul_of_one_le_right hxU he
    have s3 : x * (U + 1) * (Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x))) =
        (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by ring
    linarith
  · push_neg at hsmall
    have hqexp : (q:ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) := le_trans hqL hsmall
    obtain ⟨B, hB⟩ := exists_exceptional_zero_set cZ c₁ hc₁Z hZ' q χ
    have hmain := hPC q χ B x hB hx hqexp
    have hsumB : ‖∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) := by
      obtain ⟨hcard, hmem, -⟩ := hB
      rcases B.eq_empty_or_nonempty with hBe | ⟨β, hβ⟩
      · rw [hBe, Finset.sum_empty, norm_zero]
        exact mul_nonneg (by linarith) (Real.exp_pos _).le
      · have hBs : B = {β} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hβ, fun b hb => Finset.card_le_one.mp hcard b hb β hβ⟩
        rw [hBs, Finset.sum_singleton]
        obtain ⟨hχ1, hreg, hL0, -⟩ := hmem β hβ
        have hβ1 : 1 / 2 ≤ β := half_le_of_real_in_region hc₁20 hreg
        have hχ2 : χ ^ 2 = 1 := (hZ' q χ (β:ℂ) (zero_free_region_mono hc₁Z hreg) ⟨Or.inl hχ1, hL0⟩).1
        have hβ2 := hEB q χ β hχ2 hχ1 hL0
        exact exceptional_zero_term_bound x A q cE β hx hA hq1 hqL hcE hβ1 hβ2
    have e1 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ Real.exp (-cf * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have h1 : cf ≤ c := min_le_left _ _
      have h2 := Real.sqrt_nonneg (Real.log x)
      nlinarith
    have e2 : Real.exp (-cE * Real.sqrt (Real.log x)) ≤ Real.exp (-cf * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have h1 : cf ≤ cE := min_le_right _ _
      have h2 := Real.sqrt_nonneg (Real.log x)
      nlinarith
    have hC : C * x * Real.exp (-c * Real.sqrt (Real.log x)) ≤
        max C 0 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
      calc C * x * Real.exp (-c * Real.sqrt (Real.log x))
          ≤ max C 0 * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0) (Real.exp_pos _).le
        _ ≤ max C 0 * x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
            mul_le_mul_of_nonneg_left e1 (mul_nonneg (le_max_right _ _) hx0)
    have hE2 : 2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) ≤
        2 * x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left e2 (by linarith)
    set S : ℂ := ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ) with hS
    set a : ℂ := psiChi χ x - (if χ = 1 then (x : ℂ) else 0) with ha
    have htri : ‖a‖ ≤ ‖a + S‖ + ‖S‖ := by
      calc ‖a‖ = ‖(a + S) - S‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖a + S‖ + ‖S‖ := norm_sub_le _ _
    have hsplit : (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x)) =
        max C 0 * x * Real.exp (-cf * Real.sqrt (Real.log x)) +
        2 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by ring
    linarith
end Formalism.ZeroFreeDirichlet
