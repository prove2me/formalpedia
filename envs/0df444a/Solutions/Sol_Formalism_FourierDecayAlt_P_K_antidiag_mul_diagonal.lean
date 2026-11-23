-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.antidiag_mul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:59.466374+00:00
-- url     : https://prove2.me/submissions/c1b56ce7-84ff-4ee3-99e2-f773770ab9d4

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.K
open Matrix Finset Real Formalism.FourierDecayAlt.K
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.K
theorem _root_.solution (d : Fin n → K) :
    w0 n * diagonal d = Matrix.of fun i j => if i = Fin.rev j then d j else 0 := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [w0, Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ i = Fin.rev j := by
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  by_cases h : i = Fin.rev j
  · rw [if_pos (hiff.mpr h), if_pos h, one_mul]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, zero_mul]
end Formalism.FourierDecayAlt.P.K
