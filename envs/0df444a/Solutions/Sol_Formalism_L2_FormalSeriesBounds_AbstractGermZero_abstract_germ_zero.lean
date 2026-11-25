-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AbstractGermZero.abstract_germ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:01:05.812428+00:00
-- url     : https://prove2.me/submissions/b20006a9-45ec-4f9c-a230-4bb16f66db22

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_one_group
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_germ_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.AbstractGermZero
open Formalism.IncomingBounds
variable {C : Type} [Field C] (V : VF C)
namespace Formalism.L2.FormalSeriesBounds.AbstractGermZero
theorem _root_.solution : AbstractGermZeroCondition V := by
  intro I _ t t₂ φ φ₂ ht0 ht0₂ hφ0 hφ hL hφ0₂ hφ₂ hL₂ heq
  choose h hh0 hhI hth using fun g => one_group V (t g) (t₂ g) (φ g) (φ₂ g) (ht0₂ g) (ht0 g) (hφ0 g) (hφ g)
    (hL g) (hφ0₂ g) (hφ₂ g) (heq g)
  choose h' hh0' hhI' hth' using fun g => one_group V (t₂ g) (t g) (φ₂ g) (φ g) (ht0 g) (ht0₂ g) (hφ0₂ g)
    (hφ₂ g) (hL₂ g) (hφ0 g) (hφ g) (fun k => (heq g k).symm)
  exact Set.Subset.antisymm (germ_sub V t t₂ h ht0₂ hh0 hhI hth) (germ_sub V t₂ t h' ht0 hh0' hhI' hth')
end Formalism.L2.FormalSeriesBounds.AbstractGermZero
