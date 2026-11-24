-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.card_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:39.735802+00:00
-- url     : https://prove2.me/submissions/0c10589f-0d48-4874-b70a-384c9a2ce506

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution {ι : Type} [Fintype ι] (d : ι → ℕ) (t : ℝ) (h : ∀ u, t ≤ (d u : ℝ)) :
    (Fintype.card ι : ℝ) * t ≤ Rs d := by
  unfold Rs
  calc (Fintype.card ι : ℝ) * t = ∑ _u : ι, t := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun u _ => h u
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
