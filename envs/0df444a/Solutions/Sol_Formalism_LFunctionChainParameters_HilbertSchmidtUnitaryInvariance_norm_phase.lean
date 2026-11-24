-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.norm_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:28:32.723067+00:00
-- url     : https://prove2.me/submissions/28dc0ae4-68a5-495b-ade2-e36e9bb1c5bb

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
theorem _root_.solution (c : ι → ℂ) (hc : ∀ u, c u ≠ 0) (u u' : ι) : ‖phase c u u'‖ = 1 := by
  unfold phase
  have h1 : 0 < ‖c u‖ := norm_pos_iff.mpr (hc u)
  have h2 : 0 < ‖c u'‖ := norm_pos_iff.mpr (hc u')
  rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos h1 h2)]
  exact div_self (mul_pos h1 h2).ne'
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
