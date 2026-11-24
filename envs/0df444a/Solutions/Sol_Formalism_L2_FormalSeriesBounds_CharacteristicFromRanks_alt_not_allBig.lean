-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.alt_not_allBig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:23.66169+00:00
-- url     : https://prove2.me/submissions/520e9ffe-4a50-45a7-bbba-4d7295c7b4ac

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_alt_step

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
    (hA : Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) (g : Fin 2) : ¬ ∀ b, big g b := by
  intro hall
  exact ((alt_step big big_compl hA g 0).1 (hall _)) (hall 0)
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
