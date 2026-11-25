-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.regular_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:41.390074+00:00
-- url     : https://prove2.me/submissions/dbe3eaeb-33af-47ef-a4f0-43c6e9163e09

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
theorem _root_.solution {G : Type} [Group G] (x : Gᵐᵒᵖ) (j : G) (h : x • j = j) : x = 1 := by
  rw [MulOpposite.smul_eq_mul_unop] at h
  have : MulOpposite.unop x = 1 := by simpa using h
  simpa using congrArg MulOpposite.op this
end Formalism.L2.SG.GGMirabolic.Inhab
