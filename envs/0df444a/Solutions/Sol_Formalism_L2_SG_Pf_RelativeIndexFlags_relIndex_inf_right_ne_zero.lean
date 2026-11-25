-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.relIndex_inf_right_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:13.881035+00:00
-- url     : https://prove2.me/submissions/7000cf07-08e6-4bb2-ac00-dc6f3c8004ca

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexInfRightNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags
theorem _root_.solution {T S : Subgroup G} (h : T.relIndex S ≠ 0) (B : Subgroup G) :
    T.relIndex (S ⊓ B) ≠ 0 := by
  have h1 := Subgroup.relIndex_inter_ne_zero h B
  rw [← Subgroup.inf_relIndex_right] at h1 ⊢
  have e : T ⊓ B ⊓ (S ⊓ B) = T ⊓ (S ⊓ B) := by
    ext x; simp only [Subgroup.mem_inf]; tauto
  rwa [e] at h1
end Formalism.L2.SG.Pf.RelativeIndexFlags
