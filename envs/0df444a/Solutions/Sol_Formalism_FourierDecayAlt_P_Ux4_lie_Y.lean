-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.lie_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:33:02.292241+00:00
-- url     : https://prove2.me/submissions/54ff0ddd-621c-48e1-82f7-cd04e5eab6c1

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_three_zero_size_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_hpkBlocks

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
theorem _root_.solution (Y : B.Mat k ρ) (hY : B.inLie k ρ Y) :
    B.inLie k (j + ρ) (blk3 0 0 0 0 Y 0 0 0 0) := by
  unfold B.inLie at hY ⊢
  rw [hpkBlocks k j ρ, block3_conjTranspose, block3_mul, block3_mul, block3_add, ← block_three_zero_size_eq]
  congr 1 <;> simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.conjTranspose_zero, hY]
end Formalism.FourierDecayAlt.P.Ux4
