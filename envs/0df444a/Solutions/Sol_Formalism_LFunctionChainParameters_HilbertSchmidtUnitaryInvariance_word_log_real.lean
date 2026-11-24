-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.word_log_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:28:36.224826+00:00
-- url     : https://prove2.me/submissions/85f282f2-b023-4f69-9604-324d1d531d74

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
theorem _root_.solution : WordLogReal := by
  intro k X hX h
  have h2 : Real.log ((2 : ℝ) ^ (k - 3)) = (k - 3) * Real.log 2 := Real.log_rpow (by norm_num) _
  rw [← h2]
  rcases Nat.eq_zero_or_pos ⌈X⌉₊ with h0 | h0
  · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg (by linarith)
  · exact Real.log_le_log (by exact_mod_cast h0) ((Nat.ceil_lt_add_one hX).le.trans h)
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
