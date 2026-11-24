-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.cobF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:49.916061+00:00
-- url     : https://prove2.me/submissions/e1cfebcc-e57c-41c0-980b-bb4213442800

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Galois
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_coboundaries_le_finiteCocycles

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
open Module TensorProduct
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : CobF := by
  unfold CobF
  intros
  exact ⟨coboundaries_le_finiteCocycles ‹_›, fun c hc => hc.1⟩
end Formalism.WeaklyAdmissibleFiltrations
