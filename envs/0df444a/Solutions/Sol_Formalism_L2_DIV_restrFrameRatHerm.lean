-- Prove2me | solution 1 for Formalism.L2.DIV.restrFrameRatHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:15:45.33934+00:00
-- url     : https://prove2.me/submissions/7bfb8387-9d3c-45d9-ac04-824687c0f4e2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_restrFrameSpec
import Theorems.Thm_Formalism_L2_DIV_map_restr
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : RestrFrameRatHerm := by
  intro K _ _ _ K0 hcm hstar n d H h1 h2 E hE hE0
  have hmap : ∀ v : InfinitePlace K, (Eᴴ * H * E).map v.embedding =
      restrMetC (E.map v.embedding) (H.map v.embedding) :=
    fun v => map_restr v.embedding H E fun i a => hcm _ _ (hE0 i a)
  refine ⟨⟨?_, fun v => ⟨(restrFrameSpec K n d H h2 E hE v).1, ?_⟩⟩, ?_⟩
  · intro a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _
      (Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hstar _ (hE0 i a)) (h1 i j)) (hE0 j b)
  · rw [hmap v]
    exact (restrFrameSpec K n d H h2 E hE v).2.1
  · funext v
    rw [stdFrame, hmap v, restrFrame]
end Formalism.L2.DIV
