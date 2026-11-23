-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.rows_mul_WfrH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:45.067711+00:00
-- url     : https://prove2.me/submissions/1ecab1a7-5817-49b1-833b-1316d64bc458

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_H

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
variable {Dall D D1 : ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution {a b : ℕ} (X : Matrix (Fin a) (Fin Dall) ℂ) (X1 : Matrix (Fin b) (Fin Dall) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    (Matrix.fromRows X X1).submatrix finSumFinEquiv.symm id * (Wfr J J1)ᴴ
      = (Matrix.fromBlocks (X * J) (X * J1) (X1 * J) (X1 * J1)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [Wfr_H, ← Matrix.fromRows_mul_fromCols]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
