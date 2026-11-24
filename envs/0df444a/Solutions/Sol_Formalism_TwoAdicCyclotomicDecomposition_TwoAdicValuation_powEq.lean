-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.powEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:27.210162+00:00
-- url     : https://prove2.me/submissions/3715946a-cf77-4636-abc1-cf895fe8a8c8

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
namespace Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
theorem _root_.solution (N m : ℕ) (a : ℤ) (hz : a ^ m - 1 ≠ 0) :
    (a : ZMod (2 ^ N)) ^ m = 1 ↔ N ≤ padicValInt 2 (a ^ m - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : ((a : ZMod (2 ^ N)) ^ m = 1) ↔ (((a ^ m - 1 : ℤ)) : ZMod (2 ^ N)) = 0 := by
    push_cast; exact sub_eq_zero.symm
  rw [h0, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 := padicValInt_dvd_iff (p := 2) N (a ^ m - 1)
  push_cast at h2 ⊢
  rw [h2, or_iff_right hz]
end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
