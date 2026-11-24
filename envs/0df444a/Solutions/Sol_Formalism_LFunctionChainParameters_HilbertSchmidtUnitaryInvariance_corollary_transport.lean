-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.corollary_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:48.616926+00:00
-- url     : https://prove2.me/submissions/05294539-3616-4f4c-8a7d-9faa06375018

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_twist_invariance
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_block_count_valid
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_dim
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_block_matrix_decomposition

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
theorem _root_.solution : CorTransport := by
  intro ι _ Dall D D1 d P ga c V U J J1 A Y' Y η e del hga hc hV hU hJ hdel hD hMI hF1 hF2
  obtain ⟨g1, i1, i2, -⟩ := twist_invariance ι Dall Dall d P ga c V U hc hV hU
  obtain ⟨r1, -, j1, j2, -⟩ := block_matrix_decomposition ι Dall D D1 d (Btwist P c V U) (gaTw ga c) J J1 hJ
  have hdim : ((D + D1 : ℕ) : ℝ) = (Dall : ℝ) := by rw [frame_dim J J1 hJ]
  refine ⟨fun u => (g1 u).mpr (hga u), fun u k j => ?_, (j1 η).mpr ((i1 η).mpr hF1),
    (j2 e).mpr ((i2 e).mpr hF2), by rw [hdim]; exact hD, ?_⟩
  · rw [r1, hMI u]
    unfold Btwist
    rw [Matrix.mul_smul]
  · rw [hdim]; exact (block_count_valid Dall D del hdel).mp hD
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
