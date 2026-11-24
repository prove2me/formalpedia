-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.conj_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:40.403524+00:00
-- url     : https://prove2.me/submissions/33c3e3d0-3e01-484f-90f7-0d516bc46f01

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
variable {ι : Type} [Fintype ι] {D D' : ℕ} {d : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution (V : Matrix (Fin D') (Fin D) ℂ) (hV : Vᴴ * V = 1) (Q : Matrix (Fin D) (Fin D) ℂ) :
    (V * Q * Vᴴ) * (V * Q * Vᴴ) = V * (Q * Q) * Vᴴ := by
  have : V * Q * Vᴴ * (V * Q * Vᴴ) = V * (Q * (Vᴴ * V) * Q) * Vᴴ := by
    simp only [Matrix.mul_assoc]
  rw [this, hV, Matrix.mul_one]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
