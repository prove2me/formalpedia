-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.first_kernel_properties_of_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:41.865802+00:00
-- url     : https://prove2.me/submissions/6958bf97-666a-493c-b1a5-372d74371788

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_first_kernel_periodic_of_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_first_kernel_parseval_of_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_first_kernel_gram_of_second

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A5x6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.SingleBlockOfSteps := by
  unfold Formalism.FourierDecayAlt.A5.SingleBlockOfSteps
  intro hF hI hCD hCO hCC hG
  exact ⟨first_kernel_periodic_of_formula hF, first_kernel_gram_of_second hG, first_kernel_parseval_of_formula hF hI hCD hCO hCC⟩
end Formalism.FourierDecayAlt.P
