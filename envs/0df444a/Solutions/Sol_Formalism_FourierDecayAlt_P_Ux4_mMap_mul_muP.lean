-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.mMap_mul_muP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:33:26.384843+00:00
-- url     : https://prove2.me/submissions/cd5307e7-1093-4bf1-a4a8-41ab925cb7d5

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_w_w_mul

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
theorem _root_.solution (Z W : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) :
    mMap k j ρ Z γ * muP k j ρ W = mMap k j ρ (Z * W) γ := by
  unfold mMap muP
  rw [block3_mul]
  congr 1 <;> simp [Matrix.mul_assoc, w_w_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev]
end Formalism.FourierDecayAlt.P.Ux4
