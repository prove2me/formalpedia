-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pm_modulus_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:57.970521+00:00
-- url     : https://prove2.me/submissions/623622d7-228e-475a-b47e-89529a5538bd

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (e J : ℕ) (hJ : 1 ≤ J) :
    2 ≤ 2 ^ (e + 2 - min e (Nat.log 2 J)) ∧ 2 ^ (e + 2 - min e (Nat.log 2 J)) ≤ 2 ^ (e + 2) ∧
      2 ^ e ≤ J * 2 ^ (e + 2 - min e (Nat.log 2 J)) := by
  have hje : min e (Nat.log 2 J) ≤ e := min_le_left _ _
  have hjl : min e (Nat.log 2 J) ≤ Nat.log 2 J := min_le_right _ _
  have h2j : 2 ^ min e (Nat.log 2 J) ≤ J :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjl) (Nat.pow_log_le_self 2 (by omega))
  refine ⟨?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (e + 2 - min e (Nat.log 2 J)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc 2 ^ e = 2 ^ min e (Nat.log 2 J) * 2 ^ (e - min e (Nat.log 2 J)) := by
          rw [← pow_add, Nat.add_sub_of_le hje]
      _ ≤ J * 2 ^ (e + 2 - min e (Nat.log 2 J)) :=
          Nat.mul_le_mul h2j (Nat.pow_le_pow_right (by norm_num) (by omega))
end Formalism.RankGapBounds.LocalQuadraticParts
