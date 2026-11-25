-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.Rn_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:23.8648+00:00
-- url     : https://prove2.me/submissions/1b744bdb-a2c6-4d18-ac51-41b0a8967a3b

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_wMat_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_hpk_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_hpkBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_w_w_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux4_w_w_mul__3756fc73a85d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_skewOf_conjTranspose

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
theorem _root_.solution (x : RC k j ρ) : (Rn k j ρ x)ᴴ * Hpk k (j + ρ) * Rn k j ρ x = Hpk k (j + ρ) := by
  rw [hpkBlocks k j ρ]
  unfold Rn
  rw [block3_conjTranspose, block3_mul, block3_mul]
  have hw := wMat_conjTranspose j
  have hH := hpk_conjTranspose k ρ
  have hS := skewOf_conjTranspose x.2
  congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, hw, hH, hS,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, w_w_mul, w_w_mul', wMat_mul_self,
    neg_zero, neg_add_cancel, Matrix.smul_mul, star_neg, star_div₀, star_one, star_ofNat]
  all_goals module
end Formalism.FourierDecayAlt.P.Ux4
