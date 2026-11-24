-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_oneStepMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:28:16.995128+00:00
-- url     : https://prove2.me/submissions/d0c83cce-e2b1-44ca-bae3-f64422155922

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_cL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_one_parameter_element_base_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_oneStep_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution : OneStepMem := by
  unfold OneStepMem
  intro k r' x x' c hc g₁ hg
  exact ⟨al_oneStep_mem x x' hc hg, by rw [one_parameter_element_base_vector, al_cL_eq, three_block_last]⟩
end Formalism.FourierDecayAlt.P.B2x8
