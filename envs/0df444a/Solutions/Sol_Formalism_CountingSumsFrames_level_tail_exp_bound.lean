-- Prove2me | solution 1 for Formalism.CountingSumsFrames.level_tail_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:13.463896+00:00
-- url     : https://prove2.me/submissions/baa58f32-b69c-4c8a-b2b9-d4695cb678fc

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Theorems.Thm_Formalism_CountingSumsFrames_sum_Icc_dimHar
import Theorems.Thm_Formalism_CountingSumsFrames_tail_bound

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
theorem _root_.solution : LevelTailExp := by
  intro k' A B J La b' hk hb hLa hJ hB
  by_cases hJm : J ≤ min A B
  · rw [sum_Icc_dimHar k' A B J hJm]
    refine le_trans (tail_bound k' A B J hJm) ?_
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hD : (0:ℝ) < (B:ℝ) + k' + 1 := by positivity
    have hJB : (J:ℝ) ≤ B := by exact_mod_cast le_trans hJm (min_le_right A B)
    have ht1 : 0 ≤ 1 - (J:ℝ) / ((B:ℝ) + k' + 1) := by
      rw [sub_nonneg, div_le_one hD]; linarith
    have hexp : 1 - (J:ℝ) / ((B:ℝ) + k' + 1) ≤ Real.exp (-((J:ℝ) / ((B:ℝ) + k' + 1))) := by
      linarith [Real.add_one_le_exp (-((J:ℝ) / ((B:ℝ) + k' + 1)))]
    have hpow := pow_le_pow_left₀ ht1 hexp k'
    rw [← Real.exp_nat_mul] at hpow
    refine le_trans hpow (Real.exp_le_exp.mpr ?_)
    have hk' : (2:ℝ) ≤ k' := by exact_mod_cast hk
    have hk1 : (k':ℝ) + 1 ≠ 0 := by positivity
    have hb0 : b' ≠ 0 := hb.ne'
    have htb : La * b' / (k' + 1) / (2 * b') ≤ (J:ℝ) / ((B:ℝ) + k' + 1) := by
      calc La * b' / (k' + 1) / (2 * b') ≤ (J:ℝ) / (2 * b') :=
            div_le_div_of_nonneg_right hJ (by positivity)
        _ ≤ (J:ℝ) / ((B:ℝ) + k' + 1) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD hB
    have hs : La * b' / (k' + 1) / (2 * b') = La / (2 * ((k':ℝ) + 1)) := by
      field_simp <;> ring
    rw [hs] at htb
    have e3 : (k':ℝ) * (La / (2 * ((k':ℝ) + 1))) - La / 3 = La * ((k':ℝ) - 2) / (6 * ((k':ℝ) + 1)) := by
      field_simp <;> ring
    have n3 : 0 ≤ La * ((k':ℝ) - 2) / (6 * ((k':ℝ) + 1)) := by
      apply div_nonneg (mul_nonneg hLa (by linarith)) (by positivity)
    have m3 := mul_le_mul_of_nonneg_left htb (by linarith : (0:ℝ) ≤ k')
    nlinarith [m3, e3, n3]
  · push_neg at hJm
    rw [Finset.Icc_eq_empty_of_lt hJm, Finset.sum_empty, Nat.cast_zero]
    positivity
end Formalism.CountingSumsFrames
