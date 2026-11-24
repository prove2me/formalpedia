-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CardInsertEmbedding.L_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:36.789432+00:00
-- url     : https://prove2.me/submissions/76bd8720-c968-48b8-b8da-765e6a5ad46c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
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
open Formalism.FourierDecayAlt.P.CardInsertEmbedding
open C2x2
namespace Formalism.FourierDecayAlt.P.CardInsertEmbedding
theorem _root_.solution {m k : ℕ} (hkm : k ≤ m) (L U : Matrix (Fin m) (Fin m) ℂ) (hL : ∀ i j, i < j → L i j = 0)
    (eI f : Fin k → Fin m) (hI : ∀ t, (eI t).val = t.val) :
    (L * U).submatrix eI f = L.submatrix eI eI * U.submatrix eI f := by
  ext t s
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_emb hkm eI hI]
  intro j hj
  rw [hL _ _ (by rw [Fin.lt_def, hI]; omega), zero_mul]
end Formalism.FourierDecayAlt.P.CardInsertEmbedding
