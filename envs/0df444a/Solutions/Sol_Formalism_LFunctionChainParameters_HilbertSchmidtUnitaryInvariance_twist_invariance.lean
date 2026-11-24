-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.twist_invariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:27.129804+00:00
-- url     : https://prove2.me/submissions/759f89f6-fce2-4e6e-b0d7-d6243121ccc8

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_unitary_dimension
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_twist_hilbert_schmidt
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_twist_quadratic_form

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
theorem _root_.solution : TwInv := by
  intro ι _ D D' d B ga c V U hc hV hU
  obtain ⟨-, hq1, hq2⟩ := twist_quadratic_form ι D D' d B ga c V U hc hV hU
  obtain ⟨hk1, hk2⟩ := twist_hilbert_schmidt ι D D' d B ga c V U hc hV hU
  have hD : D' = D := unitary_dimension _ _ V hV
  refine ⟨fun u => ?_, fun η => ?_, fun e => ?_, fun Dstar η0 η1 e0 => ?_⟩
  · unfold gaTw
    have h1 : 0 < ‖c u‖ ^ 2 := by have := norm_pos_iff.mpr (hc u); positivity
    exact div_pos_iff_of_pos_right h1
  · unfold F1; rw [hq1, hq2, hD]
  · unfold F2; simp only [hk2]
  · unfold InputS; simp only [hk1, hk2, hD]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
