-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.fc_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:20.203695+00:00
-- url     : https://prove2.me/submissions/779fd53f-1a3a-4174-a55f-a53db623c575

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
theorem _root_.solution {α : Type} (s : Finset α) (f : α → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ a ∈ s, f a) = ∑ a ∈ s, Formalism.HermitianLatticesTheory.fcoord b X v (f a) := by
  exact map_sum (fcA b X v) f s
end Formalism.IndefR.LatticeTransfer.BlockMetrics
