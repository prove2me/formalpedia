-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.Rn_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:56:26.715948+00:00
-- url     : https://prove2.me/submissions/8b6e803c-b471-4e1a-8d8c-68ca9b943a5d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_mul_RnInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution (x : RC k j ρ) : (Rn k j ρ x)⁻¹ = RnInv x := Matrix.inv_eq_right_inv (Rn_mul_RnInv x)
end Formalism.FourierDecayAlt.P.Ux4
