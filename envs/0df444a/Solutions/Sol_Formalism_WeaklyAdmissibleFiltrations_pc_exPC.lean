-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.pc_exPC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:40:57.205564+00:00
-- url     : https://prove2.me/submissions/cbca2420-dc3c-4e62-afb7-7fc7491afbfd

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat

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
theorem _root_.solution : ExPC := by
  unfold ExPC
  intros
  exact ⟨PotCrysData.pcOfTop _, rfl, rfl⟩
end Formalism.WeaklyAdmissibleFiltrations
