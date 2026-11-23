-- Prove2me | solution 1 for Formalism.CountingSumsFrames.digit_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:21.587223+00:00
-- url     : https://prove2.me/submissions/cf4e5ea4-de25-4354-8518-6855ae01da11

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity

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
theorem _root_.solution (P g e : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hkey : ∀ j : ℕ, (1 - t) * ((g : ℝ) + j + 1) ≤ (P : ℝ) * ((e : ℝ) + j + 1)) :
    ∀ j : ℕ, (1 - (j : ℝ) * t) * ((g + j).choose j : ℝ) ≤ (P : ℝ) ^ j * ((e + j).choose j : ℝ) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hg : ((g + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((g : ℝ) + j + 1) * ((g + j).choose j : ℝ) := by
      have := Nat.add_one_mul_choose_eq (g + j) j
      have h' : g + (j + 1) = g + j + 1 := by ring
      rw [h']
      have hc : (((g + j + 1) * (g + j).choose j : ℕ) : ℝ)
          = (((g + j + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      linarith
    have he : ((e + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((e : ℝ) + j + 1) * ((e + j).choose j : ℝ) := by
      have := Nat.add_one_mul_choose_eq (e + j) j
      have h' : e + (j + 1) = e + j + 1 := by ring
      rw [h']
      have hc : (((e + j + 1) * (e + j).choose j : ℕ) : ℝ)
          = (((e + j + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      linarith
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hCg : (0 : ℝ) ≤ ((g + j).choose j : ℝ) := by positivity
    have hCe : (0 : ℝ) ≤ ((e + j).choose j : ℝ) := by positivity
    have hRHS : (0 : ℝ) ≤ (P : ℝ) ^ (j + 1) * ((e + (j + 1)).choose (j + 1) : ℝ) := by positivity
    push_cast
    by_cases hneg : 1 - ((j : ℝ) + 1) * t ≤ 0
    · have : (1 - ((j : ℝ) + 1) * t) * ((g + (j + 1)).choose (j + 1) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith
    push Not at hneg
    have hA : 0 ≤ 1 - (j : ℝ) * t := by nlinarith
    have hB : 0 ≤ 1 - t := by nlinarith
    have hG : (0 : ℝ) ≤ (g : ℝ) + j + 1 := by positivity

    rw [← mul_le_mul_iff_of_pos_right hj1]
    have hL : (1 - ((j : ℝ) + 1) * t) * ((g + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = (1 - ((j : ℝ) + 1) * t) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ)) := by
      rw [mul_assoc, hg]
    have hR : (P : ℝ) ^ (j + 1) * ((e + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((P : ℝ) ^ j * ((e + j).choose j : ℝ)) * ((P : ℝ) * ((e : ℝ) + j + 1)) := by
      rw [mul_assoc, he, pow_succ]; ring
    rw [hL, hR]
    have h1 : (1 - ((j : ℝ) + 1) * t) ≤ (1 - (j : ℝ) * t) * (1 - t) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) (mul_nonneg ht ht)]
    calc (1 - ((j : ℝ) + 1) * t) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ))
        ≤ ((1 - (j : ℝ) * t) * (1 - t)) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((1 - (j : ℝ) * t) * ((g + j).choose j : ℝ)) * ((1 - t) * ((g : ℝ) + j + 1)) := by ring
      _ ≤ ((P : ℝ) ^ j * ((e + j).choose j : ℝ)) * ((P : ℝ) * ((e : ℝ) + j + 1)) :=
          mul_le_mul ih (hkey j) (by positivity) (by positivity)
end Formalism.CountingSumsFrames
