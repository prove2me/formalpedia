-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.normAt_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:47.674424+00:00
-- url     : https://prove2.me/submissions/b56a5c24-b9f6-4259-9b59-9cc85effae84

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
theorem _root_.solution (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x =
      ‖(WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
end Formalism.IndefR.LatticeTransfer.BlockMetrics
