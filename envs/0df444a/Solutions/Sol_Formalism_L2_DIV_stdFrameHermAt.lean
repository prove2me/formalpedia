-- Prove2me | solution 1 for Formalism.L2.DIV.stdFrameHermAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:25.469026+00:00
-- url     : https://prove2.me/submissions/b906f8d6-264a-41a9-88b7-9d78bc294c2f

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
theorem _root_.solution : StdFrameHermAt := by
  intro K _ _ v0 n H h2
  exact ⟨fun v => (frameOfSpec n _ (h2 v)).1, (frameOfSpec n _ (h2 v0)).2⟩
end Formalism.L2.DIV
