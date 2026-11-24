-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.hs_sq_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:32.951997+00:00
-- url     : https://prove2.me/submissions/1e30bc7f-6a08-4da0-a6bf-41cca22a91e8

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.MatrixLatticeEstimates
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates
theorem _root_.solution {m n m' n' : Type} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) : hsSq (Matrix.reindex e f M) = hsSq M := by
  unfold HilbertSchmidtNormSquare.hsSq
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← f.symm.sum_comp]
  rfl
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
