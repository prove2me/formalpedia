-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.trivial_gl1_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:20:48.224738+00:00
-- url     : https://prove2.me/submissions/62077735-c31a-4183-9625-e08d7160fce3

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_superdiagonal_gl1_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic.Inhab
theorem _root_.solution : Generic psi3 (Representation.trivial ℂ (GL (Fin 1) (ZMod 3)) ℂ) := by
  refine ⟨LinearMap.id, fun h => ?_, fun u _ v => ?_⟩
  · have := LinearMap.congr_fun h 1; simp at this
  · simp [psiU, superdiagonal_gl1_eq_zero]
end Formalism.L2.SG.GGMirabolic.Inhab
