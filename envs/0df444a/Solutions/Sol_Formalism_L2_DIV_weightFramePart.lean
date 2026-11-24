-- Prove2me | solution 1 for Formalism.L2.DIV.weightFramePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:16.258669+00:00
-- url     : https://prove2.me/submissions/ab33cf2d-1c9d-48ed-a0fe-c5b07a09c759

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_majAt_eq
import Theorems.Thm_Formalism_L2_DIV_emb_mulVec
import Theorems.Thm_Formalism_L2_DIV_sum_map_eq_one
import Theorems.Thm_Formalism_L2_DIV_weightFrameSpec
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
theorem _root_.solution : WeightFramePart := by
  intro K _ _ _ n Ix _ pr t X hX ht hsum horth v hperp p x y hx
  classical
  rw [(weightFrameSpec K n Ix pr t X hX ht hsum v).2.2 x y]
  have hq0 : ∀ q, q ≠ p → (pr q).mulVec x = 0 := by
    intro q hq
    rw [← hx, Matrix.mulVec_mulVec, horth q p hq, Matrix.zero_mulVec]
  have hz : ∀ u : Fin n → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v 0 u = 0 := by
    intro u
    rw [majAt_eq]
    have : (fun i => v.embedding ((0 : Fin n → K) i)) = 0 := by funext i; simp
    rw [this, star_zero, zero_dotProduct]
  rw [Finset.sum_eq_single p (fun q _ hq => by rw [hq0 q hq, hz, mul_zero])
    (fun h => absurd (Finset.mem_univ p) h), hx]
  congr 1
  have hy : (fun i => v.embedding (y i)) =
      ∑ q, ((pr q).map v.embedding).mulVec (fun i => v.embedding (y i)) := by
    rw [← Matrix.sum_mulVec, sum_map_eq_one pr hsum, Matrix.one_mulVec]
  have hterm : ∀ q, q ≠ p → star (fun i => v.embedding (x i)) ⬝ᵥ (metOf (X v)).mulVec
      (((pr q).map v.embedding).mulVec (fun i => v.embedding (y i))) = 0 := by
    intro q hq
    have := hperp p q (Ne.symm hq) x y
    rwa [hx, majAt_eq, emb_mulVec] at this
  rw [majAt_eq, majAt_eq, emb_mulVec]
  conv_rhs => rw [hy, Matrix.mulVec_sum, dotProduct_sum]
  rw [Finset.sum_eq_single p (fun q _ hq => hterm q hq) (fun h => absurd (Finset.mem_univ p) h)]
end Formalism.L2.DIV
