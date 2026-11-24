-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.frame_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:40.989803+00:00
-- url     : https://prove2.me/submissions/853b411e-2f21-460a-8a8d-2a0e058296af

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_orth
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_orth__9fff9c147e91
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_dim
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_rows_mul_WfrH
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_uni

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
theorem _root_.solution : FrameFacts := by
  intro Dall D D1 J J1 h
  have o := frame_orth J J1 h
  have o' := frame_orth' J J1 h
  refine ⟨o, o', frame_dim J J1 h, ?_, ?_, ?_, Wfr_uni J J1 h, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
  · have : J * Jᴴ * (J * Jᴴ) = J * (Jᴴ * J) * Jᴴ := by simp only [Matrix.mul_assoc]
    rw [this, h.1, Matrix.mul_one]
  · have : J * Jᴴ * (J1 * J1ᴴ) = J * (Jᴴ * J1) * J1ᴴ := by simp only [Matrix.mul_assoc]
    rw [this, o, Matrix.mul_zero, Matrix.zero_mul]
  · rw [Wfr_mul, rows_mul_WfrH]
    have a1 : Jᴴ * (J * Jᴴ) = Jᴴ := by rw [← Matrix.mul_assoc, h.1, Matrix.one_mul]
    have a2 : J1ᴴ * (J * Jᴴ) = 0 := by rw [← Matrix.mul_assoc, o', Matrix.zero_mul]
    rw [a1, a2, h.1, o, Matrix.zero_mul, Matrix.zero_mul]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
