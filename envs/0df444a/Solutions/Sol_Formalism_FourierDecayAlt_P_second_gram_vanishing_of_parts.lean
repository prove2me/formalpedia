-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.second_gram_vanishing_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:55.42227+00:00
-- url     : https://prove2.me/submissions/07f1908f-14be-402b-828d-b1e0d0bef0fd

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_second_vanishing_of_triple_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_second_gram_of_kernel_gram

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
theorem _root_.solution : Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps := by
  unfold Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps Formalism.FourierDecayAlt.A5.A2
  intro hG hM hTF hAvg hEnd
  exact ⟨second_gram_of_kernel_gram hG hM, second_vanishing_of_triple_form hTF hAvg hEnd⟩
end Formalism.FourierDecayAlt.P
