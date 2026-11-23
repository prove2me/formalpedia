-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.mulW_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:56.444836+00:00
-- url     : https://prove2.me/submissions/c8efd797-d207-41b9-8a22-1a6516535520

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_antidiag_mul_diagonal

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
theorem _root_.solution (a : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    (a * (w0 n * diagonal d) : Matrix (Fin n) (Fin n) K) i j = a i (Fin.rev j) * d j := by
  rw [antidiag_mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.K
