-- Prove2me | solution 1 for Formalism.FG.shift_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:40.33156+00:00
-- url     : https://prove2.me/submissions/43a56783-8d5c-40d8-afca-92a742f5ef05

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Theorems.Thm_Formalism_FG_ShiftFEAux_idMod2
import Theorems.Thm_Formalism_FG_ShiftFEAux_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.FG
open ShiftFEAux
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.ShiftFunEq.{u} := by
  intro K _ _ l hl m _ σ
  exact ⟨idMod2 hl.two_le, fun j => main hl σ j⟩
end Formalism.FG
