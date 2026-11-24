-- Prove2me | solution 1 for Formalism.L2.DIV.quotEqRestrRat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:14.055895+00:00
-- url     : https://prove2.me/submissions/fdefac3f-9ae1-41fe-a7d8-83fe5d8dd8d0

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
theorem _root_.solution : QuotEqRestrRat := by
  intro K _ _ _ K0 hcm n d H hH E Pr hE hP
  funext v
  exact quot_eq_restr_of v H (hH v) E Pr (fun i a => hcm _ _ (hE i a)) hP
end Formalism.L2.DIV
