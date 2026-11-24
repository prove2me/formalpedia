-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.even_val_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:17.147407+00:00
-- url     : https://prove2.me/submissions/e5702abd-0e34-4571-b3d9-e3039fb1d20e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution {d : ℕ} [NeZero d] (hd : Even d) (b : ZMod d) :
    Even (b + 1).val ↔ ¬ Even b.val := by
  have hd2 : 2 ≤ d := by
    obtain ⟨k, hk⟩ := hd
    have := NeZero.ne d
    omega
  haveI : Fact (1 < d) := ⟨by omega⟩
  rw [ZMod.val_add, ZMod.val_one]
  have hb := ZMod.val_lt b
  rcases Nat.lt_or_ge (b.val + 1) d with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.even_add_one]
  · have heq : b.val + 1 = d := by omega
    rw [heq, Nat.mod_self]
    refine iff_of_true ⟨0, rfl⟩ fun hbe => ?_
    have h2 : Even (b.val + 1) := by rw [heq]; exact hd
    rw [Nat.even_add_one] at h2
    exact h2 hbe
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
