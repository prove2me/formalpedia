-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.fc_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:31.877639+00:00
-- url     : https://prove2.me/submissions/75eaedca-3d21-4429-895c-0af16d59da9d

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
theorem _root_.solution (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  have h : Formalism.HermitianLatticesTheory.vecAt b v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
  simp only [Formalism.HermitianLatticesTheory.fcoord, h, Matrix.mulVec_smul]
end Formalism.IndefR.LatticeTransfer.BlockMetrics
