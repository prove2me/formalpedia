-- Prove2me | solution 1 for Formalism.CountingSumsFrames.dimHar_ratio_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:21.622925+00:00
-- url     : https://prove2.me/submissions/94294cd1-5d4a-49f7-8a8c-37ed5541c601

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_pos_real
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_succ_mul_real

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
open Finset Filter Topology
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (k' al be : ℕ) (hk : 2 ≤ k') (hal : 0 < al) :
    1 ≤ (dimHar k' al be : ℝ) / ((dimPol k' al : ℝ) * dimPol k' be)
      * (((be : ℝ) + k') / ((k' : ℝ) - 1)) := by
  have hk2 : (2 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have pa := dimPol_pos_real k' al
  have pb := dimPol_pos_real k' be
  rcases Nat.eq_zero_or_pos be with h0 | hbe
  · subst h0
    have : dimHar k' al 0 = dimPol k' al * dimPol k' 0 := by simp [dimHar]
    rw [this]; push_cast
    rw [div_self (by positivity), one_mul, le_div_iff₀ hk1]; simp
  · obtain ⟨a0, rfl⟩ : ∃ a0, al = a0 + 1 := ⟨al - 1, by omega⟩
    obtain ⟨b0, rfl⟩ : ∃ b0, be = b0 + 1 := ⟨be - 1, by omega⟩
    have hle : dimPol k' a0 * dimPol k' b0 ≤ dimPol k' (a0 + 1) * dimPol k' (b0 + 1) := by
      unfold dimPol
      exact Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
    have hH : dimHar k' (a0 + 1) (b0 + 1)
        = dimPol k' (a0 + 1) * dimPol k' (b0 + 1) - dimPol k' a0 * dimPol k' b0 := by
      simp [dimHar]
    rw [hH, Nat.cast_sub hle]
    push_cast
    have p0 := dimPol_pos_real k' a0
    have p1 := dimPol_pos_real k' b0
    have eX := dimPol_succ_mul_real k' a0
    have eY := dimPol_succ_mul_real k' b0
    set X := (dimPol k' (a0 + 1) : ℝ)
    set Y := (dimPol k' (b0 + 1) : ℝ)
    set x := (dimPol k' a0 : ℝ)
    set y := (dimPol k' b0 : ℝ)
    have hA : (0 : ℝ) < (a0 : ℝ) + 1 := by positivity
    have hB0 : (0 : ℝ) ≤ (b0 : ℝ) := by positivity
    have hXx : x ≤ X := by
      have : x * ((a0 : ℝ) + 1) ≤ X * ((a0 : ℝ) + 1) := by
        rw [eX]; nlinarith
      exact le_of_mul_le_mul_right this hA
    rw [div_mul_div_comm, one_le_div (by positivity)]
    have hYB : 0 ≤ Y * ((b0 : ℝ) + 1) := by positivity
    have h1 : x * (Y * ((b0 : ℝ) + 1)) ≤ X * (Y * ((b0 : ℝ) + 1)) := mul_le_mul_of_nonneg_right hXx hYB
    have hXY : 0 ≤ X * Y := by positivity
    nlinarith
end Formalism.CountingSumsFrames
