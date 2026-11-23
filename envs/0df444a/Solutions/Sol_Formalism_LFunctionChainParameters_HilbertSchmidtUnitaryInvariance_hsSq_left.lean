-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.hsSq_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:59.290595+00:00
-- url     : https://prove2.me/submissions/160f3a7e-91c1-4ce5-8205-f6732e98a5c2

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_eq_re


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
theorem _root_.solution {a a' b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) (S : Matrix (Fin a') (Fin a) ℂ)
    (hS : Sᴴ * S = 1) : hsSq (S * M) = hsSq M := by
  rw [hsSq_eq_re, hsSq_eq_re, conjTranspose_mul]
  have : Mᴴ * Sᴴ * (S * M) = Mᴴ * (Sᴴ * S) * M := by simp only [Matrix.mul_assoc]
  rw [this, hS, Matrix.mul_one]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
