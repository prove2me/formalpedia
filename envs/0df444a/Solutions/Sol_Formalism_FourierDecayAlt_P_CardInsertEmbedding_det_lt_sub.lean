-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CardInsertEmbedding.det_lt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:35:01.780398+00:00
-- url     : https://prove2.me/submissions/85f1ac6c-df47-4d74-9d20-4cedbfeeb0a9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding

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
theorem _root_.solution {m k : ℕ} (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) (eI : Fin k → Fin m)
    (hI : ∀ t, (eI t).val = t.val) : (l.submatrix eI eI).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp only [Matrix.submatrix_apply, hl.2, Finset.prod_const_one]
  · intro t t' h
    simp only [Matrix.submatrix_apply]
    apply hl.1
    rw [Fin.lt_def, hI, hI]
    exact OrderDual.toDual_lt_toDual.mp h
end Formalism.FourierDecayAlt.P.CardInsertEmbedding
