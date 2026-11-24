-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.maj_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:42.39781+00:00
-- url     : https://prove2.me/submissions/8f9ea77d-0803-48aa-92fd-7765101bec93

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
theorem _root_.solution (x y y' : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (y + y') = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x y' := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
end Formalism.IndefR.LatticeTransfer.BlockMetrics
