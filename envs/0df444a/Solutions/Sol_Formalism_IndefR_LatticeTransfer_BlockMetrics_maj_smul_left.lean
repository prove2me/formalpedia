-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.maj_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:47.258871+00:00
-- url     : https://prove2.me/submissions/d65b4488-18fd-4977-82c0-79797711ba0a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_fc_smul

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
theorem _root_.solution (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (a • x) y = starRingEnd ℂ (v.embedding a) * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply]
  ring
end Formalism.IndefR.LatticeTransfer.BlockMetrics
