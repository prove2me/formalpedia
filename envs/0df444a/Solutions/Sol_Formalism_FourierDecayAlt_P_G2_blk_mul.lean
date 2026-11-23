-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G2.blk_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:53.10352+00:00
-- url     : https://prove2.me/submissions/ddc61e14-b707-483d-a826-c36626a93d1b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G2
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G2
theorem _root_.solution {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]
end Formalism.FourierDecayAlt.P.G2
