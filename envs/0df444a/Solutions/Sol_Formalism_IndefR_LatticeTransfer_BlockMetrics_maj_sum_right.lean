-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.maj_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:42.248836+00:00
-- url     : https://prove2.me/submissions/53a0ebf9-744e-4648-989d-d8be14947863

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_fc_smul
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_fc_sum

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
theorem _root_.solution {α : Type} (s : Finset α) (c : α → K) (f : α → V) (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (∑ a ∈ s, c a • f a) =
      ∑ a ∈ s, v.embedding (c a) * Formalism.HermitianLatticesTheory.majAt b X v x (f a) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring
end Formalism.IndefR.LatticeTransfer.BlockMetrics
