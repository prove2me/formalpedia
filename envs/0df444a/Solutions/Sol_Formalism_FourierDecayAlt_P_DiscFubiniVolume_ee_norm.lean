-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.ee_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:53.171204+00:00
-- url     : https://prove2.me/submissions/ed9f56be-5df4-49e9-934c-58e1feb41946

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory intervalIntegral Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution (u t : ℝ) : ‖ee u t‖ = 1 := Complex.norm_exp_I_mul_ofReal (u * t)
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
