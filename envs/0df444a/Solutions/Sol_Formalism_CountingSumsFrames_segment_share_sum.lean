-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_share_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:55.853619+00:00
-- url     : https://prove2.me/submissions/11c16189-833e-49ff-b52e-8544d894f7c9

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

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
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegShareSum := by
  have he2 : (1 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨fun t Y epsP eps hY heps hP => ?_, fun Jn N N₁ Y t κ hY hN₁ hN hκ1 hκ => ?_⟩
  · have hY0 : 0 < Y := by linarith
    have hS : ∑ i, eps i ≤ (t : ℝ) * (28 / Y) := by
      calc ∑ i, eps i ≤ ∑ _i : Fin t, 28 / Y := Finset.sum_le_sum fun i _ => heps i
        _ = (t : ℝ) * (28 / Y) := by simp
    have hexp : Real.exp (2 / Y) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by
      rw [div_le_iff₀ hY0]
      linarith)
    have hexp0 : 0 < Real.exp (2 / Y) := Real.exp_pos _
    have h28 : 0 ≤ (t : ℝ) * (28 / Y) := by positivity
    have key : Real.exp (2 / Y) * (∑ i, eps i) ≤ Real.exp 2 * ((t : ℝ) * (28 / Y)) := by
      rcases le_or_gt (∑ i, eps i) 0 with hneg | hpos
      · nlinarith [hexp0, hneg, h28, Real.exp_pos 2]
      · calc Real.exp (2 / Y) * (∑ i, eps i) ≤ Real.exp 2 * (∑ i, eps i) :=
            mul_le_mul_of_nonneg_right hexp hpos.le
          _ ≤ Real.exp 2 * ((t : ℝ) * (28 / Y)) := mul_le_mul_of_nonneg_left hS (Real.exp_pos 2).le
    have h5 : (5 : ℝ) / Y ≤ 28 / Y := div_le_div_of_nonneg_right (by norm_num) hY0.le
    have h28' : 28 / Y ≤ Real.exp 2 * (28 / Y) := le_mul_of_one_le_left (by positivity) he2
    constructor
    · have e1 : 2 * Real.exp 2 * ((t : ℝ) + 1) * 28 / Y =
          2 * (Real.exp 2 * ((t : ℝ) * (28 / Y))) + 2 * (Real.exp 2 * (28 / Y)) := by ring
      rw [e1]
      linarith
    · have e1 : 2 * Real.exp 2 * 28 * ((t : ℝ) + 1) / Y =
          2 * Real.exp 2 * ((t : ℝ) * (28 / Y) + 28 / Y) := by ring
      rw [e1]
      have hsum' : (∑ i, eps i) + epsP ≤ (t : ℝ) * (28 / Y) + 28 / Y := by linarith
      have h2e : 0 < 2 * Real.exp 2 := by positivity
      exact mul_le_mul_of_nonneg_left hsum' h2e.le
  · have hY0 : 0 < Y := by linarith
    have hN₁R : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
    have hper : ∀ j, κ j ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y := by
      intro j
      have htj : (0 : ℝ) ≤ t j := Nat.cast_nonneg _
      by_cases hc : (N₁ : ℝ) ≤ Y
      · have h1 := hκ hc j
        have h2 : 2 * Real.exp 2 * 28 * ((t j : ℝ) + 1) / Y ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y := by
          apply div_le_div_of_nonneg_right _ hY0.le
          nlinarith [mul_nonneg (mul_nonneg (Real.exp_pos 2).le (by linarith : (0:ℝ) ≤ t j + 1))
            (by linarith : (0:ℝ) ≤ N₁ - 1)]
        linarith
      · push_neg at hc
        have hX : (1 : ℝ) ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) := by nlinarith [he2, htj]
        have h1 : (1 : ℝ) ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y := by
          rw [le_div_iff₀ hY0]
          nlinarith [hX, hN₁R, hc]
        linarith [hκ1 j]
    refine ⟨hper, ?_⟩
    calc ∑ j, κ j ≤ ∑ j, 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y :=
          Finset.sum_le_sum fun j _ => hper j
      _ = 56 * Real.exp 2 * N₁ / Y * ∑ j, ((t j : ℝ) + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 56 * Real.exp 2 * N₁ / Y * N := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast hN
      _ = 56 * Real.exp 2 * N * N₁ / Y := by ring
end Formalism.CountingSumsFrames
