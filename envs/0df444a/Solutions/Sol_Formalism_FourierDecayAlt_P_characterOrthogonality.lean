-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.characterOrthogonality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:25.704953+00:00
-- url     : https://prove2.me/submissions/6f26b49b-0f74-4895-ba1d-2617ad460b8e

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_sum_over_C
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_coker

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
theorem _root_.solution : Formalism.FourierDecayAlt.A5.CharOrth := by
  intro K _ _ _ R ψ hD n Z hZ hdet μ
  have := finite_coker hD Z hZ hdet
  rw [sum_over_C hD.selfDual μ]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P
