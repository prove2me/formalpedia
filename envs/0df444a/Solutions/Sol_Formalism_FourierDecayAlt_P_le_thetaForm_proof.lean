-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.le_thetaForm_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:17.324396+00:00
-- url     : https://prove2.me/submissions/7bab516e-1a73-458c-808e-abdac35469ac

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EnergyEstimateFromParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.ThetaForm := by
  intro ε σ hε v
  simp only [LE.th]
  have hv := Real.exp_pos v
  have h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹ := by
    rw [Real.exp_neg]
    field_simp
    try ring
  rw [h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
end Formalism.FourierDecayAlt.P
