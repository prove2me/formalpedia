-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.superdiagonal_gl1_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:51.187942+00:00
-- url     : https://prove2.me/submissions/859a5f4d-ac61-4451-86ea-a71ddb180fd8

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab

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
theorem _root_.solution (x : Matrix (Fin 1) (Fin 1) (ZMod 3)) : superdiag 1 x = 0 := by
  simp [superdiag]
end Formalism.L2.SG.GGMirabolic.Inhab
