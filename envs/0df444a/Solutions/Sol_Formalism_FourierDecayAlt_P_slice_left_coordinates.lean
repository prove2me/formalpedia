-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.slice_left_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:55.443408+00:00
-- url     : https://prove2.me/submissions/fa47be5a-14b5-4496-bf5c-5d4175297abe

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_embG_mul_mMap

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
theorem _root_.solution : Formalism.FourierDecayAlt.U.SliceLeft := by
  intro k p s ρ σ d ξ Z γ y
  unfold gaXi
  rw [← embG_mul_mMap]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.1) (Rn k (p + s) ρ ξ.1.1)⁻¹, Rn_mul_inv, Matrix.one_mul]
end Formalism.FourierDecayAlt.P
