-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.additive_char_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:37.144896+00:00
-- url     : https://prove2.me/submissions/18a34a0a-8ce8-48e1-8691-abfecab7dd84

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_additive_char_one_ne_one

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
theorem _root_.solution : psi3 ≠ 1 := by
  intro h; apply additive_char_one_ne_one; rw [h]; rfl
end Formalism.L2.SG.GGMirabolic.Inhab
