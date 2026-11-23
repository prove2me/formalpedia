-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.characterOrthogonalityDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:27.333728+00:00
-- url     : https://prove2.me/submissions/dc954cce-baf1-4398-bda1-60ffc5f710b3

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_dual
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x3_sum_over_dual__ff440f43ee65
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_card_dual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_coker_sep
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
theorem _root_.solution : Formalism.FourierDecayAlt.A5.CharOrthDual := by
  intro K _ _ _ R ψ hD n Z hZ hdet
  have := finite_coker hD Z hZ hdet
  refine ⟨finite_dual hD.selfDual, fun x => ?_⟩
  rw [sum_over_dual' hD.selfDual (coker_sep R Z hdet) x,
    card_dual hD.selfDual (coker_sep R Z hdet)]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P
