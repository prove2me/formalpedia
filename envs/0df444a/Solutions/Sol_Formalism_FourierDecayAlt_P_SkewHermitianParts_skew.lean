-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:01.500852+00:00
-- url     : https://prove2.me/submissions/3f32b793-1dea-483a-aa9b-6a22b95f51f9

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.SkewHermitianParts
open AnisotropicColumnSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SkewHermitianParts
theorem _root_.solution {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (X *ᵥ v) w = -herm (Hpk k r) v (X *ᵥ w) := by
  have e : Hpk k r * X = -(Xᴴ * Hpk k r) := eq_neg_of_add_eq_zero_right hX
  unfold herm
  rw [Matrix.mulVec_mulVec, e, Matrix.neg_mulVec, dotProduct_neg, Matrix.star_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
end Formalism.FourierDecayAlt.P.SkewHermitianParts
