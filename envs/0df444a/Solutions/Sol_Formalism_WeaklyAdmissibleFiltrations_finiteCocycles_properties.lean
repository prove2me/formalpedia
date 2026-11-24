-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.finiteCocycles_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:43.08626+00:00
-- url     : https://prove2.me/submissions/ed6f8eab-bf7b-4aa8-9a36-03d4f4b852f5

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Galois
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_cobF
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_torsFreeT
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_cocyclesFunctorial_holds
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_imFLe

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
theorem _root_.solution : CobF ∧ TorsFreeT ∧ CocyclesFunctorial ∧ ImFLe :=
  ⟨cobF, torsFreeT, cocyclesFunctorial_holds, imFLe⟩
end Formalism.WeaklyAdmissibleFiltrations
