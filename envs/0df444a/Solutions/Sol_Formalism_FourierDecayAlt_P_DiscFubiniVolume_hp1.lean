-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.hp1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:53.018868+00:00
-- url     : https://prove2.me/submissions/d089a4aa-650e-439d-a568-920ea648e409

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
theorem _root_.solution (t : ℝ) : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * t)) t :=
  ((hasDerivAt_pow 2 t).const_sub 1).congr_deriv (by norm_num)
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
