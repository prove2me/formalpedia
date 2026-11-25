-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.jc_stepJCont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:46.057147+00:00
-- url     : https://prove2.me/submissions/448bc20a-f542-4b0a-97d3-b27e62117293

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_ae_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_cont_tau
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_aesm_J

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution : Formalism.FourierDecayAlt.B.StepJCont := by
  intro k r Wp Wq _ _ _ _ _ _ D A hI hCC F hF
  refine ⟨jc_ae_integrable D hI hCC hF, ?_, ?_⟩
  · filter_upwards [jc_ae_integrable D hI hCC hF] with q hq
    exact (jc_cont_tau D F _ hq).continuousOn
  · intro τ _
    exact jc_aesm_J D (jc_cont hF) τ
end Formalism.FourierDecayAlt.P.B7
