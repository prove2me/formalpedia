-- Prove2me | solution 1 for Formalism.FG.witt_char_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:40.336933+00:00
-- url     : https://prove2.me/submissions/c9445f13-21d8-4672-9172-b6f6604db3e3

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Theorems.Thm_Formalism_FG_WittVectorsCharZero_zlToW_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG
open Formalism.FG.WittVectorsCharZero
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.WittCharZero := by
  intro l _
  refine ⟨fun m n h => ?_⟩
  have h1 : ((m : ℤ_[l])) = (n : ℤ_[l]) :=
    zlToW_injective l (by rw [map_natCast, map_natCast]; exact h)
  exact_mod_cast h1
end Formalism.FG
