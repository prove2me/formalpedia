-- Prove2me | solution 1 for Formalism.L2.DIV.weightFrameSpec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:42.519956+00:00
-- url     : https://prove2.me/submissions/af32a137-2d28-499e-b9f6-37f98d47c8b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_majAt_eq
import Theorems.Thm_Formalism_L2_DIV_emb_mulVec
import Theorems.Thm_Formalism_L2_DIV_frameOfSpec
import Theorems.Thm_Formalism_L2_DIV_weightMet_form
import Theorems.Thm_Formalism_L2_DIV_weightMet_posDef

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
theorem _root_.solution : WeightFrameSpec := by
  intro K _ _ _ n Ix _ pr t X hX ht hsum v
  have hs := frameOfSpec n _ (weightMet_posDef pr t X hX ht hsum v)
  refine ⟨hs.1, hs.2, fun x y => ?_⟩
  have hm : metOf (weightFrame pr t X v) = weightMet pr t X v := hs.2
  rw [majAt_eq, hm, weightMet_form]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [majAt_eq, emb_mulVec, emb_mulVec]
end Formalism.L2.DIV
