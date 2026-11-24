-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.zj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:39:32.983433+00:00
-- url     : https://prove2.me/submissions/fb65c42d-e94c-43ac-8e0a-351129271460

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_symmetricScalarBlockMatrix_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block2_det_upper_triangular

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
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (Z q : Matrix (Fin s) (Fin s) ℂ) :
    Zj a b H (Z * q) = Zj a b H Z * ((blk2 1 (Matrix.of b) 0 1)⁻¹ * blk2 1 0 0 q * blk2 1 (Matrix.of b) 0 1) := by
  have hU : blk2 1 (Matrix.of b) 0 1 * (blk2 1 (Matrix.of b) 0 1)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [block2_det_upper_triangular]; simp)
  have hD : blk2 H 0 0 (Z * q) = blk2 H 0 0 Z * blk2 1 0 0 q := by
    rw [symmetricScalarBlockMatrix_mul]; simp
  unfold Zj
  rw [hD]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (blk2 1 (Matrix.of b) 0 1) (blk2 1 (Matrix.of b) 0 1)⁻¹, hU, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Ux4
