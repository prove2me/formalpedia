-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.lie_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:31:13.139073+00:00
-- url     : https://prove2.me/submissions/efbb69ca-2a37-40ca-a293-f8b5413d936a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_three_zero_size_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_wMat_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_hpkBlocks
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
theorem _root_.solution (Q : Matrix (Fin j) (Fin j) ℂ) :
    B.inLie k (j + ρ) (blk3 (k := k) (ρ := ρ) Q 0 0 0 0 0 0 0 (-(G.wMat j * Qᴴ * G.wMat j))) := by
  unfold B.inLie
  have hw := wMat_conjTranspose j
  rw [hpkBlocks k j ρ, block3_conjTranspose, block3_mul, block3_mul, block3_add, ← block_three_zero_size_eq]
  congr 1 <;> simp only [Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hw, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, w_w_mul, wMat_mul_self, add_neg_cancel]
  all_goals abel
end Formalism.FourierDecayAlt.P.Ux4
