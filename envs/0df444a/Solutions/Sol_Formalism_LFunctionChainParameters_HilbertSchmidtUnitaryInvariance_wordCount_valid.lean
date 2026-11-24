-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.wordCount_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:29.719936+00:00
-- url     : https://prove2.me/submissions/c7aa67b9-da70-4b5c-92b5-bff906e239b7

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_card_mul_le

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
theorem _root_.solution : WordCount := by
  intro ι _ d C0 Gam sg Dstar hC hG hs hD hcard hd
  have h1 : C0 * Gam ^ 2 / sg ≤ (Fintype.card ι : ℝ) := by rw [hcard]; exact Nat.le_ceil _
  have h2 := card_mul_le d _ hd
  have h3 : Dstar / sg = (C0 * Gam ^ 2 / sg) * (Dstar / Gam ^ 2 / C0) := by field_simp
  rw [h3]
  exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) h2
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
