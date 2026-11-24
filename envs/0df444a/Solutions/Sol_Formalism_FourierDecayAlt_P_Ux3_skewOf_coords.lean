-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.skewOf_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:08.387026+00:00
-- url     : https://prove2.me/submissions/9c3b197a-fda7-4fa3-a307-43822cef70d9

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_apply_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_apply_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_apply_gt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : Sᴴ = -S) : skewOf (skewCoords S) = S := by
  ext a b
  rcases lt_trichotomy a b with h | rfl | h
  · rw [skewOf_apply_lt _ _ _ h]
    rfl
  · rw [skewOf_apply_diag]
    have h1 : star (S a a) = -S a a := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS a) a
    have h2 := congrArg Complex.re h1
    simp at h2
    apply Complex.ext
    · simp
      linarith
    · simp [skewCoords]
  · rw [skewOf_apply_gt _ _ _ h]
    have h1 : star (S b a) = -S a b := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS a) b
    simp only [skewCoords]
    rw [h1, neg_neg]
end Formalism.FourierDecayAlt.P.Ux3
