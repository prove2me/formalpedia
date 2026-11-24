-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.WfrS_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:38.430489+00:00
-- url     : https://prove2.me/submissions/160f157d-b8f9-4083-b5dd-3dafd7ccdf45

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
theorem _root_.solution {Dall D D1 : ℕ} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : (WfrS J J1)ᴴ * WfrS J J1 = 1 := by
  unfold WfrS
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_conjTranspose,
    conjTranspose_conjTranspose, Matrix.fromCols_mul_fromRows, h.2.2]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
