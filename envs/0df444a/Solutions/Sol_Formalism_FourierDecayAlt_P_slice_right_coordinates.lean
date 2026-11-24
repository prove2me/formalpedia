-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.slice_right_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:00:38.261799+00:00
-- url     : https://prove2.me/submissions/4394d29c-8af1-4637-b76d-bad083eab9f0

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_mMap_mul_embG

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Ux4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.SliceRight := by
  intro k p s ρ σ d ξ Z γ y
  unfold gaXi
  rw [← mMap_mul_embG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.2) (Rn k (p + s) ρ ξ.1.2)⁻¹, Rn_mul_inv, Matrix.one_mul]
end Formalism.FourierDecayAlt.P
