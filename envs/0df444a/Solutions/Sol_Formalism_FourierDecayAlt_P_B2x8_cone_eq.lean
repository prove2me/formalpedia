-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.cone_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:09:25.913569+00:00
-- url     : https://prove2.me/submissions/cb28f807-859a-443a-abe6-9005aa018b94

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_parametrisation_eq_scaled_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_parametrisation_map_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_parametrisation_map_measure

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
theorem _root_.solution : coneMeas k r' = ((μx.prod (volume : Measure (HPar k r')))).map (Ψt k r') := by
  unfold coneMeas
  have e : (fun p : ℂ × HPar k r' => p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')) =
      Ψt k r' ∘ cm1Θ k r' := funext parametrisation_eq_scaled_sum
  rw [e, ← Measure.map_map Ψt_meas parametrisation_map_measurable, parametrisation_map_measure]
end Formalism.FourierDecayAlt.P.B2x8
