-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.exists_jj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:47.326447+00:00
-- url     : https://prove2.me/submissions/e24e6f7f-189f-4ac3-be5c-7fa106a583d7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (d : ℕ) [NeZero d] : ∃ jj : ZMod d ≃ Fin d, ∀ a, jj (a + 1) = jj a + 1 := ⟨(ZMod.finEquiv d).symm.toEquiv, fun a => by
  first
  | simp
  | (show (ZMod.finEquiv d).symm (a + 1) = (ZMod.finEquiv d).symm a + 1
     rw [map_add, map_one])⟩
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
