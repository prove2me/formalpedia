-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.card_zmod3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:42.799814+00:00
-- url     : https://prove2.me/submissions/1f103843-a46c-4dea-b5ad-4d157a5315e0

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
theorem _root_.solution : 3 ≤ Fintype.card (ZMod 3) := by simp
end Formalism.L2.SG.GGMirabolic.Inhab
