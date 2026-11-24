-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_gram_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:27.216485+00:00
-- url     : https://prove2.me/submissions/0a1ef2c9-9114-45ad-b189-4a1df379ddeb

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
theorem _root_.solution {I α : Type} [Fintype α] {ι : I → Type} (B : ∀ i, Matrix α (ι i) ℂ)
    (ga : I → ℝ) (i : I) (hi : 0 ≤ ga i) : KdG B ga i = ((ga i : ℝ) : ℂ) • ((B i)ᴴ * B i) := by
  unfold KdG KpG
  rw [Real.sqrt_mul_self hi]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
