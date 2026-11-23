-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.right_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:40.737979+00:00
-- url     : https://prove2.me/submissions/250d8682-edca-4c0c-8696-26be8117cfd8

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_Wmul_apply

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
theorem _root_.solution {b : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (hd : ∀ x, d x ≠ 0)
    (h : (w0 n * diagonal d) * b = w0 n * diagonal d) : b = 1 := by
  ext x j
  have e := congrFun (congrFun h (Fin.rev x)) j
  have e1 : (w0 n * Matrix.diagonal d : Matrix (Fin n) (Fin n) K) (Fin.rev x) j =
      ((w0 n * Matrix.diagonal d) * 1 : Matrix (Fin n) (Fin n) K) (Fin.rev x) j := by
    rw [Matrix.mul_one]
  rw [e1, Wmul_apply, Wmul_apply, Fin.rev_rev] at e
  exact mul_left_cancel₀ (hd x) e
end Formalism.FourierDecayAlt.P.K
