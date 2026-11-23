-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G1.hasDerivAt_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:52.697367+00:00
-- url     : https://prove2.me/submissions/fe1137c5-bcf9-4d62-9410-46b0173f7d7a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_hasDerivAt_inv_lin

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
    HasDerivAt (fun ξ : ℂ => c / (ξ * Q) / ξ) (-(2 * c / (a * Q * a * a))) a := by
  have h := (hasDerivAt_inv_lin c Q a ha hQ).div (hasDerivAt_id' a) ha
  refine h.congr_deriv ?_
  field_simp
  ring
end Formalism.FourierDecayAlt.P.G1
