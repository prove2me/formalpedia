-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.fcoord_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:42.085498+00:00
-- url     : https://prove2.me/submissions/31aa5c62-2c7c-4019-97a8-0054d5d1c8a3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.BlockMetrics
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
namespace Formalism.IndefR.LatticeTransfer.BlockMetrics
theorem _root_.solution (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (φ x) =
      ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v).mulVec
        (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (φ x) =
      ((LinearMap.toMatrix b b φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← LinearMap.toMatrix_mulVec_repr b b φ x, RingHom.map_mulVec]
    rfl
  simp only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]
end Formalism.IndefR.LatticeTransfer.BlockMetrics
