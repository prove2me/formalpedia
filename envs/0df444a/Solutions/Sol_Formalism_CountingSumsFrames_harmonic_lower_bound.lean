-- Prove2me | solution 1 for Formalism.CountingSumsFrames.harmonic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:51.91033+00:00
-- url     : https://prove2.me/submissions/4ece1cf4-beba-4292-ad82-25b5a2b80404

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_mono
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_mul_deg

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
theorem _root_.solution : HarLower := by
  intro k' al be
  by_cases h : al = 0 ∨ be = 0
  · have hd : dimHar k' al be = dimPol k' al * dimPol k' be := by
      unfold dimHar; rw [if_pos h, Nat.sub_zero]
    rw [hd]
    have hP : (0:ℝ) ≤ ((dimPol k' al * dimPol k' be : ℕ) : ℝ) := Nat.cast_nonneg _
    rcases Nat.eq_zero_or_pos (be + k') with h0 | h0
    · have h0' : ((be:ℝ) + k') = 0 := by exact_mod_cast h0
      rw [h0', div_zero]; exact hP
    · have hpos : (0:ℝ) < (be:ℝ) + k' := by exact_mod_cast h0
      rw [mul_div_assoc]
      calc _ ≤ ((dimPol k' al * dimPol k' be : ℕ) : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left _ hP
            rw [div_le_one hpos]; linarith [(Nat.cast_nonneg be : (0:ℝ) ≤ be)]
        _ = _ := mul_one _
  · push_neg at h
    obtain ⟨ha, hb⟩ := h
    have hle1 : dimPol k' (al - 1) ≤ dimPol k' al := dimPol_mono k' (Nat.sub_le _ _)
    have hrec := dimPol_mul_deg k' (be - 1)
    rw [show be - 1 + 1 = be by omega] at hrec
    have hd : dimHar k' al be = dimPol k' al * dimPol k' be - dimPol k' (al - 1) * dimPol k' (be - 1) := by
      unfold dimHar; rw [if_neg (by omega)]
    have hle2 : dimPol k' (al - 1) * dimPol k' (be - 1) ≤ dimPol k' al * dimPol k' be :=
      Nat.mul_le_mul hle1 (dimPol_mono k' (Nat.sub_le _ _))
    rw [hd, Nat.cast_sub hle2]
    push_cast
    have hbe : (0:ℝ) < be := by exact_mod_cast Nat.pos_of_ne_zero hb
    have hpos : (0:ℝ) < (be:ℝ) + k' := by positivity
    have hrec' : (dimPol k' (be - 1) : ℝ) * ((be:ℝ) + k') = dimPol k' be * be := by exact_mod_cast hrec
    have hle1' : (dimPol k' (al - 1) : ℝ) ≤ dimPol k' al := by exact_mod_cast hle1
    set Pa := (dimPol k' al : ℝ)
    set Pb := (dimPol k' be : ℝ)
    set Pa1 := (dimPol k' (al - 1) : ℝ)
    set Pb1 := (dimPol k' (be - 1) : ℝ)
    have h3 : Pa1 * (Pb * be) ≤ Pa * (Pb * be) := mul_le_mul_of_nonneg_right hle1' (by positivity)
    have h4 : Pa1 * (Pb1 * ((be:ℝ) + k')) = Pa1 * (Pb * be) := by rw [hrec']
    rw [div_le_iff₀ hpos]
    have e : (Pa * Pb - Pa1 * Pb1) * ((be:ℝ) + k') =
        Pa * Pb * k' + (Pa * (Pb * be) - Pa1 * (Pb1 * ((be:ℝ) + k'))) := by ring
    rw [e, h4]
    linarith
end Formalism.CountingSumsFrames
