-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.normAt_eq_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:08.773137+00:00
-- url     : https://prove2.me/submissions/42184212-842e-4806-af7d-d85baf296103

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_self

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
    Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [maj_self, Complex.ofReal_re, Real.sqrt_sq]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  exact Real.sqrt_nonneg _
end Formalism.IndefR.LatticeTransfer.BlockMetrics
