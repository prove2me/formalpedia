-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pow_two_pow_pm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:14.140991+00:00
-- url     : https://prove2.me/submissions/d5b4d067-b54e-4d78-a1c4-ca61297ff694

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_four_not_dvd_odd_sq_add_one
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_sq_sub_one_dvd_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (j : ℕ) : ∀ (x : ℤ), Odd x → ∀ m : ℕ, 1 ≤ m →
    (((2 : ℤ) ^ (m + j) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (m + j) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1)) := by
  induction j with
  | zero => intro x _ m _; simp
  | succ j ih =>
    intro x hx m hm
    have hy : Odd (x ^ (2 ^ j)) := hx.pow
    have hpow : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
    have hnot : ¬ (2 : ℤ) ^ (m + (j + 1)) ∣ (x ^ (2 ^ j)) ^ 2 + 1 := by
      intro h
      apply four_not_dvd_odd_sq_add_one _ hy
      refine dvd_trans ?_ h
      have : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 (by omega)
    rw [hpow, ← ih x hx m hm, show m + (j + 1) = m + j + 1 by omega,
      ← sq_sub_one_dvd_iff _ hy (m + j) (by omega)]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h (by rw [show m + j + 1 = m + (j + 1) by omega]; exact hnot)
    · intro h
      exact Or.inl h
end Formalism.RankGapBounds.LocalQuadraticParts
