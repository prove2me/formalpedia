-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G1.hasDerivAt_inv_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:04.03393+00:00
-- url     : https://prove2.me/submissions/2cf2fa08-b638-4b8f-8ff8-b52fd0ea66e4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G1
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G1
theorem _root_.solution (c Q a : ℂ) (ha : a ≠ 0) (hQ : Q ≠ 0) :
    HasDerivAt (fun ξ : ℂ => c / (ξ * Q)) (-(c / (a * Q) / a)) a := by
  have h := (hasDerivAt_const a c).div ((hasDerivAt_id' a).mul_const Q) (mul_ne_zero ha hQ)
  refine h.congr_deriv ?_
  field_simp
  ring
end Formalism.FourierDecayAlt.P.G1
