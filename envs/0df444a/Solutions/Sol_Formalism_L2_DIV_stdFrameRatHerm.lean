-- Prove2me | solution 1 for Formalism.L2.DIV.stdFrameRatHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:08:40.101216+00:00
-- url     : https://prove2.me/submissions/391e5a1d-31ba-421a-99bc-5e410014110a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_frameOfSpec

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
theorem _root_.solution : StdFrameRatHerm := by
  intro K _ _ _ K0 n H h1 h2
  exact ⟨h1, fun v => frameOfSpec n _ (h2 v)⟩
end Formalism.L2.DIV
