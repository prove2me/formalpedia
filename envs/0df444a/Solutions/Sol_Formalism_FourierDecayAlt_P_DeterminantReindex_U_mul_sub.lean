-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantReindex.U_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:43.901024+00:00
-- url     : https://prove2.me/submissions/541b3cac-745f-4dae-b46d-8e3cf76ff680

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
import Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_sum_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.DeterminantReindex
open C2x2 CardInsertEmbedding
namespace Formalism.FourierDecayAlt.P.DeterminantReindex
theorem _root_.solution {m k : ℕ} (hkm : k ≤ m) (M U : Matrix (Fin m) (Fin m) ℂ) (hU : ∀ i j, j < i → U i j = 0)
    (e f : Fin k → Fin m) (hf : ∀ t, (f t).val = t.val) :
    (M * U).submatrix e f = M.submatrix e f * U.submatrix f f := by
  ext t s
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_emb hkm f hf]
  intro j hj
  rw [hU _ _ (by rw [Fin.lt_def, hf]; omega), mul_zero]
end Formalism.FourierDecayAlt.P.DeterminantReindex
