-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.inv_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:13:40.194797+00:00
-- url     : https://prove2.me/submissions/8d7f5c54-6f4d-4606-a4b0-e6f77110b1cd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_inv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution {n : ℕ} : ContinuousOn (fun x : Matrix (Fin n) (Fin n) ℂ => x⁻¹) {x | IsUnit x.det} := by
  simp only [inv_eq]
  exact (continuous_id.matrix_det.continuousOn.inv₀ (fun x hx => IsUnit.ne_zero hx)).smul
    continuous_id.matrix_adjugate.continuousOn
end Formalism.FourierDecayAlt.P.B2x2
