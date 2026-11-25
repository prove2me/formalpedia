-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.le_thetaMono_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:41:20.715674+00:00
-- url     : https://prove2.me/submissions/0505b024-2bcb-47d2-9a4e-ce52f5264f6c

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
theorem _root_.solution : Formalism.FourierDecayAlt.LE.ThetaMono := by
  intro σ ε ε' x hσ hε hεε' hx
  simp only [LE.th]
  have hε' : 0 < ε' := by linarith
  have hb : 0 < x / (x + ε') := by positivity
  exact Real.rpow_le_rpow hb.le (by gcongr) hσ
end Formalism.FourierDecayAlt.P
