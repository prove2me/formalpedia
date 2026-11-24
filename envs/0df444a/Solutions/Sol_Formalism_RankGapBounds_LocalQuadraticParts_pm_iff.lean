-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:01.876788+00:00
-- url     : https://prove2.me/submissions/5d59f70b-5c32-4bb4-9435-bcfa7c0da0e9

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pow_two_pow_pm_iff

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
theorem _root_.solution (e j : ℕ) (hj : j ≤ e) (x : ℤ) (hx : Odd x) :
    (((2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ (e + 2 - j) ∣ x - 1 ∨ (2 : ℤ) ^ (e + 2 - j) ∣ x + 1)) := by
  have h := pow_two_pow_pm_iff j x hx (e + 2 - j) (by omega)
  rw [show e + 2 - j + j = e + 2 by omega] at h
  exact h
end Formalism.RankGapBounds.LocalQuadraticParts
