-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.elementary_unipotent_is_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:49.507409+00:00
-- url     : https://prove2.me/submissions/dcc24ad1-3b9f-4196-8a10-a746f48fda0f

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
theorem _root_.solution : IsUni 2 u12 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> simp [u12]
  · fin_cases i <;> fin_cases j <;> simp_all [u12]
end Formalism.L2.SG.GGMirabolic.Inhab
