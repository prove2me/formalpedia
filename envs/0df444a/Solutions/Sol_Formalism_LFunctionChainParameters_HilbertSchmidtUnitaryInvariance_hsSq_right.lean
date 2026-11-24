-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.hsSq_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:41.596925+00:00
-- url     : https://prove2.me/submissions/78200739-6ce5-4f24-8e32-2686fbd1c49f

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_hsSq_left
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_conjTranspose


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
theorem _root_.solution {a b b' : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) (T : Matrix (Fin b) (Fin b') ℂ)
    (hT : T * Tᴴ = 1) : hsSq (M * T) = hsSq M := by
  rw [← hsSq_conjTranspose (M * T), conjTranspose_mul, hsSq_left _ _ (by simpa using hT),
    hsSq_conjTranspose]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
