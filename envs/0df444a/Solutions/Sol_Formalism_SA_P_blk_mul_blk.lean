-- Prove2me | solution 1 for Formalism.SA.P.blk_mul_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:20:11.067337+00:00
-- url     : https://prove2.me/submissions/586f584e-71bf-4257-883d-504fd40caaa1

import Definitions.Def_Formalism_LatticeRigidity_StatementA
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_BlockEquationHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open Matrix Formalism.SA.A
variable {R : Type} [CommRing R] {m : ℕ}
namespace Formalism.SA.P
theorem _root_.solution (A A' : Matrix (Fin (m+1)) (Fin (m+1)) R) (b c b' c' : Fin (m+1) → R) (d d' : R) :
    blk A b c d * blk A' b' c' d' =
      blk (A * A' + vecMulVec b c') (A *ᵥ b' + d' • b) (c ᵥ* A' + d • c') (c ⬝ᵥ b' + d * d') := by
  unfold blk
  rw [fromBlocks_multiply]
  congr 1
  · ext i j
    simp [Matrix.mul_apply, vecMulVec]
  · ext i j
    simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
  · ext i j
    simp [Matrix.mul_apply, vecMul, dotProduct]
  · ext i j
    simp [Matrix.mul_apply, dotProduct]
end Formalism.SA.P
