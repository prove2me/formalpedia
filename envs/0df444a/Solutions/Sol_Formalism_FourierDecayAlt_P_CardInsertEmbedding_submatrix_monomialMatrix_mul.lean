-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CardInsertEmbedding.submatrix_monomialMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:37.653864+00:00
-- url     : https://prove2.me/submissions/9ac9f034-6924-4941-90cb-a9d676803dd0

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
theorem _root_.solution {m k n : ℕ} (hkn : k = n) (hnm : n ≤ m) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) (eR eI f : Fin k → Fin m) (hI : ∀ t, (eI t).val = t.val)
    (hR : ∀ t, ∃ j0 : Fin m, j0.val < n ∧ w j0 = eR t) :
    (C2.monoP w d * M).submatrix eR f = (C2.monoP w d).submatrix eR eI * M.submatrix eI f := by
  ext t s
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  obtain ⟨j0, hj0, hw⟩ := hR t
  rw [sum_emb (by omega) eI hI]
  intro j hj
  simp only [C2.monoP, Matrix.of_apply]
  rw [if_neg, zero_mul]
  intro e; rw [← hw] at e; have := w.injective e; rw [← this] at hj; omega
end Formalism.FourierDecayAlt.P.CardInsertEmbedding
