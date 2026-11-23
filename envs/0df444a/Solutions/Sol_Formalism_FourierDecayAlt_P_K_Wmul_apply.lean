-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.Wmul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:49.331312+00:00
-- url     : https://prove2.me/submissions/4d981971-6910-4de7-8053-79dbb8c366e4

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
theorem _root_.solution (c : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    ((w0 n * diagonal d) * c : Matrix (Fin n) (Fin n) K) i j = d (Fin.rev i) * c (Fin.rev i) j := by
  rw [antidiag_mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp
  · intro k _ hk
    simp only [Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro h
    apply hk
    rw [h, Fin.rev_rev]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.K
