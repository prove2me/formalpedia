-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.sqrt_gaTw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:28:34.184683+00:00
-- url     : https://prove2.me/submissions/123ee239-7b64-4b4d-8dbc-a79e380db82f

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
theorem _root_.solution (ga : ι → ℝ) (c : ι → ℂ) (hc : ∀ u, c u ≠ 0) (u u' : ι) :
    Real.sqrt (gaTw ga c u * gaTw ga c u') = Real.sqrt (ga u * ga u') / (‖c u‖ * ‖c u'‖) := by
  unfold gaTw
  have h1 : 0 < ‖c u‖ := norm_pos_iff.mpr (hc u)
  have h2 : 0 < ‖c u'‖ := norm_pos_iff.mpr (hc u')
  have : ga u / ‖c u‖ ^ 2 * (ga u' / ‖c u'‖ ^ 2) = ga u * ga u' / (‖c u‖ * ‖c u'‖) ^ 2 := by
    field_simp
  rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
