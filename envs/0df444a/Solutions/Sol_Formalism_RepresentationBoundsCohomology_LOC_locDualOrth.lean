-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.locDualOrth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:48.697089+00:00
-- url     : https://prove2.me/submissions/fc1fee3e-8935-441c-9b6b-bd12df331cf5

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_LocDualOrth
import Theorems.Thm_P2M_Formalism_RepresentationBoundsCohomology_LOC_mem_annih__37a7288d66f3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution : StatLocDualOrth.{u} := by
  intro O A HT' _ _ _ _ _ _ _ pr HfT' Q ℓ e' hF hO hL y hy
  rw [mem_annih']
  intro κ hκ
  obtain ⟨x, hx, hxκ⟩ := hL κ hκ
  rw [map_smul, LinearMap.smul_apply, ← LinearMap.map_smul, ← hxκ, Q.cup, hO _ hy _ (hF hx), map_zero]
end Formalism.RepresentationBoundsCohomology.LOC
