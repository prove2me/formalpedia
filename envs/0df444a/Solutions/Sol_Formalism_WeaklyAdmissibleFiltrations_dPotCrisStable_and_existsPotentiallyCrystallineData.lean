-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.dPotCrisStable_and_existsPotentiallyCrystallineData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:14.297572+00:00
-- url     : https://prove2.me/submissions/b1dc9ee3-4d67-483d-9960-7f74c8361b36

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pc_dpcrisStable
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pc_exPC

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
theorem _root_.solution : DpcrisStable ∧ ExPC := ⟨pc_dpcrisStable, pc_exPC⟩
end Formalism.WeaklyAdmissibleFiltrations
