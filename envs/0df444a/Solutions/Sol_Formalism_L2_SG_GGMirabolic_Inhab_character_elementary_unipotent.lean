-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.character_elementary_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:47.999361+00:00
-- url     : https://prove2.me/submissions/f9e21e6f-e6df-4f0b-8f75-ad23b2001d88

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
theorem _root_.solution : psiU psi3 u12 = psi3 1 := by
  simp [psiU, superdiag, u12, Fin.sum_univ_two]
end Formalism.L2.SG.GGMirabolic.Inhab
