-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.mirabolic_bound_gl2_f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:50.351604+00:00
-- url     : https://prove2.me/submissions/41538d94-7556-418c-a859-7cf4a6fe7896

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
theorem _root_.solution : ∏ i ∈ Finset.Ico 1 2, (Fintype.card (ZMod 3) ^ i - 1) = 2 ∧
    Module.finrank ℂ ℂ = 1 := by
  refine ⟨?_, Module.finrank_self ℂ⟩
  simp
end Formalism.L2.SG.GGMirabolic.Inhab
