-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.hpart1_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:03.152787+00:00
-- url     : https://prove2.me/submissions/9115b716-7338-4bd6-9d22-5ef296b3ecd7

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_hpk_inv
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796


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
theorem _root_.solution {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) : hpart1 (Hpk k r) X = X := by
  have e : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  unfold hpart1
  rw [Qx8.hpk_inv, Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul,
    sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num
end Formalism.FourierDecayAlt.P.SkewHermitianParts
