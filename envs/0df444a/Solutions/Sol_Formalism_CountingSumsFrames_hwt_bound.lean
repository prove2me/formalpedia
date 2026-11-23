-- Prove2me | solution 1 for Formalism.CountingSumsFrames.hwt_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:50.831028+00:00
-- url     : https://prove2.me/submissions/4ee1f378-9026-4140-b614-fe74c922e135

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Theorems.Thm_Formalism_CountingSumsFrames_weylDim_hwt
import Theorems.Thm_Formalism_CountingSumsFrames_prod_le_pow_mul_prod
import Theorems.Thm_Formalism_CountingSumsFrames_fin_sub_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (m A c B : ℕ) (t : ℝ) (ht : 0 ≤ t) (hA : (c : ℝ) ≤ t * A) (hB : (c : ℝ) ≤ t * B) :
    (weylDim (m + 2) (hwt m (A + c) (B + c)) : ℝ) ≤ (1 + t) ^ (2 * m + 1) * (weylDim (m + 2) (hwt m A B) : ℝ) := by
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [weylDim_hwt, weylDim_hwt]
  push_cast
  have f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := fun j => by positivity
  have f2 : ∀ j : Fin m, 0 ≤ ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := by
    intro j; have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have P1 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ t * (((j : ℕ) : ℝ) + 1) := by positivity
      nlinarith)
  have P2 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (fin_sub_pos m j).le
      have := fin_sub_pos m j
      have : 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ)) := by positivity
      nlinarith)
  have P3 : ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ t * ((m : ℝ) + 1) := by positivity
    nlinarith
  have g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => f1 j
  have g2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => f2 j
  have f3 : 0 ≤ ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) := by positivity
  have k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => by positivity
  have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have k3 : 0 ≤ (1 + t) ^ m := by positivity
  calc _ ≤ ((1 + t) ^ m * ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
        ((1 + t) ^ m * ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
        ((1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring
end Formalism.CountingSumsFrames
