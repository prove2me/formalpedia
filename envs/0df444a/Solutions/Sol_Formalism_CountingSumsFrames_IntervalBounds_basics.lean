-- Prove2me | solution 1 for Formalism.CountingSumsFrames.IntervalBounds.basics
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:16.403798+00:00
-- url     : https://prove2.me/submissions/043498b3-77ac-410f-88ef-a1ca2896f677

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_ApolarComparisonExponent
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_IntervalCleanDepthBound
import Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_one_le_log_of_three_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.IntervalBounds
open ParamsIProof
namespace Formalism.CountingSumsFrames.IntervalBounds
theorem _root_.solution (C C₀ : ℝ) (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ)
    (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (h : PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar) :
    (1 : ℝ) ≤ N ∧ (1 : ℝ) ≤ N₁ ∧ (5 : ℝ) ≤ k ∧ (1 : ℝ) ≤ J ∧ (J : ℝ) ≤ N ∧ (25 : ℝ) ≤ p ∧
    1 ≤ (p : ℝ) ^ G' ∧ 0 < a ∧ 1 ≤ Real.log a ∧ 1 ≤ Real.logb p a ∧ 0 ≤ logBaseP p a k ∧
    logBaseP p a k ≤ 3 * Real.logb p a ∧ 1 ≤ logScale C₀ N₁ a ∧ (N : ℝ) ≤ k ∧ (N₁ : ℝ) ^ 2 ≤ k ∧
    0 ≤ D ∧ 1 ≤ b' := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24⟩ := h
  unfold logScale at *
  have hC0 : 0 < C := by linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast g4
  have hN1 : (1 : ℝ) ≤ N₁ := by exact_mod_cast g5
  have hkn : 2 * N₁ + 3 ≤ k := by omega
  have hk : (2 : ℝ) * N₁ + 3 ≤ k := by exact_mod_cast hkn
  have hk5 : (5 : ℝ) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast g7
  have hJN : (J : ℝ) ≤ N := by exact_mod_cast g8
  have hY0 : 0 < Y := by linarith
  have hk2 : (25 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk5]
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ g2
  have hkp : (k : ℝ) ^ 2 ≤ p := le_trans (le_mul_of_one_le_right (by positivity) hY2) g3
  have hp25 : (25 : ℝ) ≤ p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hQ : 1 ≤ (p : ℝ) ^ G' := one_le_pow₀ hp1.le
  have hab : (p : ℝ) * b' < a := (lt_div_iff₀ g17).mp g18
  have ha0 : 0 < a := lt_trans (by positivity) hab
  have hNY : 1 ≤ (N : ℝ) * Y := one_le_mul_of_one_le_of_one_le hN g2
  have hCN : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hN1)
  have hLa0 : 0 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := by
    have := Real.log_nonneg hNY
    linarith
  have hL0 : 0 ≤ Real.log a := by
    by_contra hneg
    rw [not_le] at hneg
    have : C₀ * (N₁ : ℝ) ^ 2 * Real.log a < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  have ha1 : 1 ≤ a := (Real.log_nonneg_iff ha0).mp hL0
  have hl0 : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 ha1
  have hD0 : 0 ≤ D := le_trans (by positivity) g22
  have hcS : 8 ≤ cStar := by linarith
  have hNcl : 0 ≤ (N : ℝ) * cl := by positivity
  have hncl : 0 ≤ (n' : ℝ) * cl := by positivity
  have hX : 8 ≤ cStar + N * cl + n' * cl := by linarith
  have hk3 : 1 ≤ (k : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hQ4 : 1 ≤ ((p : ℝ) ^ G') ^ 4 := one_le_pow₀ hQ
  have hb1 : 1 ≤ b' := le_trans
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hk3) hN) hQ4)
      (by linarith)) g2) g24
  have hpa : (p : ℝ) ≤ a := le_trans (le_mul_of_one_le_right hp0.le hb1) hab.le
  have hL1 : 1 ≤ Real.log a := one_le_log_of_three_le a (by linarith)
  have hl1 : 1 ≤ Real.logb p a := by
    rw [← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0 ha0).mpr hpa
  have hka : (k : ℝ) ≤ a := by
    have : (k : ℝ) ≤ (k : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hlg0 : 0 ≤ logBaseP p a k := by
    unfold logBaseP
    have := Real.logb_nonneg hp1 (show 1 ≤ 8 * a + k by linarith)
    linarith
  have hlg : logBaseP p a k ≤ 3 * Real.logb p a := by
    unfold logBaseP
    have hh : Real.logb p (8 * a + k) ≤ Real.logb p (p * a) :=
      (Real.logb_le_logb hp1 (by linarith) (by positivity)).mpr (by
        have : 25 * a ≤ p * a := mul_le_mul_of_nonneg_right hp25 ha0.le
        linarith)
    rw [Real.logb_mul hp0.ne' ha0.ne', Real.logb_self_eq_one hp1] at hh
    linarith
  have hLaN : (N₁ : ℝ) ^ 2 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := by
    have h3 : 1 ≤ C₀ * Real.log a := one_le_mul_of_one_le_of_one_le hC₀ hL1
    have := le_mul_of_one_le_right (by positivity : (0:ℝ) ≤ (N₁ : ℝ) ^ 2) h3
    linarith
  have hLa1 : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := one_le_mul_of_one_le_of_one_le hCN hL1
  generalize C₀ * (N₁ : ℝ) ^ 2 * Real.log a = La at *
  have hLa2 : 1 ≤ La ^ 2 := one_le_pow₀ hLa1
  have hNk : (N : ℝ) ≤ k := by
    have h3 : 1 ≤ C * La ^ 2 := one_le_mul_of_one_le_of_one_le hC hLa2
    have := le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ N) h3
    linarith
  have sq_level_le_degree : (N₁ : ℝ) ^ 2 ≤ k := by
    have h3 : 1 ≤ C * N * La := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC hN) hLa1
    have := le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ La) h3
    linarith
  exact ⟨hN, hN1, hk5, hJ1, hJN, hp25, hQ, ha0, hL1, hl1, hlg0, hlg, hLa1, hNk, sq_level_le_degree, hD0, hb1⟩
end Formalism.CountingSumsFrames.IntervalBounds
