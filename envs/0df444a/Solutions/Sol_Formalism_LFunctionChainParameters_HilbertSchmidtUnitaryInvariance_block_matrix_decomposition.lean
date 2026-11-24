-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.block_matrix_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:27.080809+00:00
-- url     : https://prove2.me/submissions/368246bc-16a9-4282-8222-814a1aaa420b

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_twist_invariance
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_gaTw_one
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_uni
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_isUni_one
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Brow_eq

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
theorem _root_.solution : RowsBlock := by
  intro ι _ Dall D D1 d B ga J J1 h
  obtain ⟨-, i1, i2, i3⟩ := twist_invariance ι Dall (D + D1) d B ga (fun _ => 1) (Wfr J J1)
    (fun _ => 1) (fun _ => one_ne_zero) (Wfr_uni J J1 h) (fun _ => isUni_one _)
  rw [gaTw_one, ← Brow_eq] at i1 i2 i3
  refine ⟨fun u k j => ?_, fun u k j => ?_, i1, i2, i3⟩
  · unfold Brow; rw [Wfr_mul]; simp
  · unfold Brow; rw [Wfr_mul]; simp
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
