-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.pc_dpcrisStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:51.430245+00:00
-- url     : https://prove2.me/submissions/cc200466-7ffd-4d09-ae3a-e1a39fc70ebd

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pc_Dpcris_stable

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
theorem _root_.solution : DpcrisStable := by
  intros
  apply pc_Dpcris_stable
  all_goals assumption
end Formalism.WeaklyAdmissibleFiltrations
