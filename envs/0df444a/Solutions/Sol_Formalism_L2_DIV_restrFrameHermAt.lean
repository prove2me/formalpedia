-- Prove2me | solution 1 for Formalism.L2.DIV.restrFrameHermAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:15:37.34948+00:00
-- url     : https://prove2.me/submissions/9f2a4fb9-3f93-494a-ac26-957df2dd093a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_restrFrameSpec
import Theorems.Thm_Formalism_L2_DIV_map_restr

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
theorem _root_.solution : RestrFrameHermAt := by
  intro K _ _ _ v0 hv0 n d H h2 E hE
  refine ⟨fun v => (restrFrameSpec K n d H h2 E hE v).1, ?_⟩
  rw [map_restr v0.embedding H E fun i a => hv0 _]
  exact (restrFrameSpec K n d H h2 E hE v0).2.1
end Formalism.L2.DIV
