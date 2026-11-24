-- Prove2me | solution 1 for Formalism.L2.DIV.quotEqRestrAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:41.186622+00:00
-- url     : https://prove2.me/submissions/a54092d8-c72c-423e-87ec-1126a22e3b21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_quot_eq_restr_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : QuotEqRestrAt := by
  intro K _ _ _ v0 hv0 n d H hH E Pr hP
  exact quot_eq_restr_of v0 H hH E Pr (fun i a => hv0 _) hP
end Formalism.L2.DIV
