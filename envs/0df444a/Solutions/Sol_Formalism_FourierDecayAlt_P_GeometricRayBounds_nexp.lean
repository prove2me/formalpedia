-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GeometricRayBounds.nexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:08.97437+00:00
-- url     : https://prove2.me/submissions/19eac840-649f-456f-9c05-772b65686f92

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GeometricRayBounds
namespace Formalism.FourierDecayAlt.P.GeometricRayBounds
theorem _root_.solution (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x
end Formalism.FourierDecayAlt.P.GeometricRayBounds
