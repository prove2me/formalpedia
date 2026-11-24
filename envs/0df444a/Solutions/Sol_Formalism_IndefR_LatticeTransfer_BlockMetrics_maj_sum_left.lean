-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.maj_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:42.159843+00:00
-- url     : https://prove2.me/submissions/5c8305cb-d45a-4be3-8605-0c09185ab792

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
theorem _root_.solution {α : Type} (s : Finset α) (c : α → K) (f : α → V) (y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (∑ a ∈ s, c a • f a) y =
      ∑ a ∈ s, star (v.embedding (c a)) * Formalism.HermitianLatticesTheory.majAt b X v (f a) y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring
end Formalism.IndefR.LatticeTransfer.BlockMetrics
