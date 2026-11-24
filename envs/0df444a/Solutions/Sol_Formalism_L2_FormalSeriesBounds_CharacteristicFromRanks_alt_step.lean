-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.alt_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:31.476186+00:00
-- url     : https://prove2.me/submissions/a637e9b4-35fa-4dd1-9496-b0a0ad3019c4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_even_val_succ

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
theorem _root_.solution {d : ℕ} [NeZero d] (big : Fin 2 → ZMod d → Prop)
    (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (hA : Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) (g : Fin 2) :
    ∀ b, big g (b + 1) ↔ ¬ big g b := by
  intro b
  have h0 : ∀ a, big 0 a ↔ Even a.val := hA.2
  have h1 : ∀ a, big 1 a ↔ ¬ big 0 a := fun a => by simpa using big_compl 0 a
  fin_cases g
  · show big 0 (b + 1) ↔ ¬ big 0 b
    rw [h0, h0, even_val_succ hA.1]
  · show big 1 (b + 1) ↔ ¬ big 1 b
    rw [h1, h1, h0, h0, even_val_succ hA.1]
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
