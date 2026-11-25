-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dualSpan_true_hc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:40:17.443472+00:00
-- url     : https://prove2.me/submissions/1bfc5c53-c7ad-4173-9cd7-e889d8b3255b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mem_of_kills

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A5x3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.DualSpan := by
  intro K _ R ψ h C _ _ _ ι _ lam μ hμ
  apply mem_of_kills h
  intro c hc
  exact hμ c fun j => hc _ (Submodule.subset_span ⟨j, rfl⟩)
end Formalism.FourierDecayAlt.P
