-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.Rn_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:52.437161+00:00
-- url     : https://prove2.me/submissions/fe4568fb-908b-4b33-84ef-cf6ad5115cf1

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_wMat_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_hpk_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_hpkBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_w_w_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux6_w_w_mul__e0ef0e90c794
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_skewOf_conjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
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
end Formalism.FourierDecayAlt.P.Ux6
