-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.min_le_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:19.072794+00:00
-- url     : https://prove2.me/submissions/832d4c35-8604-44b5-af8d-2f7dbb185f2f

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution (x y r : ℝ) (hx : 0 < x) (hy : 0 < y) (hr : |r| ≤ y) :
    (min 1 (x / y)) ^ (5 / 4 : ℝ) ≤ psi ⌊2 * r / x⌋ := by
  unfold psi
  set a : ℤ := ⌊2 * r / x⌋ with ha
  have key : min 1 (x / y) ≤ 4 / (|(a : ℝ)| + 1) := by
    rcases le_or_gt |(a : ℝ)| 2 with h | h
    · refine (min_le_left _ _).trans ?_
      rw [le_div_iff₀ (by positivity)]
      linarith
    · refine (min_le_right _ _).trans ?_
      have h1 : (a : ℝ) ≤ 2 * r / x := Int.floor_le _
      have h2 : 2 * r / x < a + 1 := Int.lt_floor_add_one _
      have h3 : |(a : ℝ)| - 1 ≤ |2 * r / x| := by
        rcases le_or_gt 0 (a : ℝ) with h0 | h0
        · rw [abs_of_nonneg h0]
          have : (a : ℝ) ≤ |2 * r / x| := h1.trans (le_abs_self _)
          linarith
        · rw [abs_of_neg h0]
          have ha1 : (a : ℝ) + 1 ≤ 0 := by
            have : a < 0 := by exact_mod_cast h0
            have : a + 1 ≤ 0 := by omega
            exact_mod_cast this
          have : -(2 * r / x) ≤ |2 * r / x| := neg_le_abs _
          linarith
      have h4 : |2 * r / x| = 2 * |r| / x := by
        rw [abs_div, abs_mul, abs_of_pos hx]; norm_num
      rw [h4] at h3
      have h3' : (3 : ℝ) ≤ |(a : ℝ)| := by
        rw [← Int.cast_abs] at h ⊢
        have h6 : (2 : ℤ) < |a| := by exact_mod_cast h
        have h7 : (3 : ℤ) ≤ |a| := by omega
        exact_mod_cast h7
      have h5 : (|(a : ℝ)| + 1) / 2 ≤ 2 * y / x := by
        have : 2 * |r| / x ≤ 2 * y / x := by
          apply div_le_div_of_nonneg_right _ hx.le; linarith
        linarith
      rw [div_le_div_iff₀ hy (by positivity)]
      rw [le_div_iff₀ hx] at h5
      nlinarith
  have h0 : 0 ≤ min 1 (x / y) := le_min zero_le_one (by positivity)
  exact Real.rpow_le_rpow h0 key (by norm_num)
end Formalism.NuclearRankWeightBounds.P
