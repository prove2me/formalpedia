-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Wfr_uni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:09.125385+00:00
-- url     : https://prove2.me/submissions/5bf21b95-5588-45de-864f-f0f5e1f3af2b

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_orth
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_orth__9fff9c147e91
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_H
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_rows_mul_WfrH

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
theorem _root_.solution (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : IsUni (Wfr J J1) := by
  constructor
  · rw [Wfr_H]
    unfold Wfr
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, h.2.2]
    simp
  · show (Matrix.fromRows Jᴴ J1ᴴ).submatrix finSumFinEquiv.symm id * (Wfr J J1)ᴴ = 1
    rw [rows_mul_WfrH, h.1, h.2.1, frame_orth J J1 h, frame_orth' J J1 h, Matrix.fromBlocks_one,
      Matrix.submatrix_one_equiv]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
