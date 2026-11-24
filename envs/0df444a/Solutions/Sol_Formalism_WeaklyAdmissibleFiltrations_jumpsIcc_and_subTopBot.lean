-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.jumpsIcc_and_subTopBot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:52.983878+00:00
-- url     : https://prove2.me/submissions/7414c1a4-32ec-4dba-afa0-cbd58f272fa6

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_jumpsIcc
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_subTopBot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open FilPhi
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : JumpsIcc ∧ SubTopBot := ⟨jumpsIcc, subTopBot⟩
end Formalism.WeaklyAdmissibleFiltrations
