-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.inf_relIndex_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:39.892962+00:00
-- url     : https://prove2.me/submissions/78bb2655-8272-4096-819b-0d03de19e2a2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (H N L : Subgroup G) (hL : L ≤ N) :
    (H ⊓ N).relIndex L = H.relIndex L := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hL x.2⟩⟩
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
