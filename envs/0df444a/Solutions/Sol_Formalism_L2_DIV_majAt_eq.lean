-- Prove2me | solution 1 for Formalism.L2.DIV.majAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:06.173351+00:00
-- url     : https://prove2.me/submissions/5b113445-127d-4609-9f17-c7906e19ef6e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      star (fun i => v.embedding (x i)) ⬝ᵥ (metOf (X v)).mulVec (fun i => v.embedding (y i)) := by
  have h1 : ∀ u : Fin n → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v u =
      fun i => v.embedding (u i) := by
    intro u; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1, metOf]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl
end Formalism.L2.DIV
