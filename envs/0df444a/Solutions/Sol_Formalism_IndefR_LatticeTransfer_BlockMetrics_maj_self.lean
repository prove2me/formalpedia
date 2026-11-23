-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.maj_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:47.160848+00:00
-- url     : https://prove2.me/submissions/2f9b2d45-b254-4aaf-8b9c-15e7ff2719cf

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
    Formalism.HermitianLatticesTheory.majAt b X v x x = ((Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 : ℝ) : ℂ) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' _
end Formalism.IndefR.LatticeTransfer.BlockMetrics
