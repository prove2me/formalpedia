-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantReindex.sign_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:44.925377+00:00
-- url     : https://prove2.me/submissions/b89396be-08c5-48f0-9ce8-310ddf2a3911

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex

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
theorem _root_.solution {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp
end Formalism.FourierDecayAlt.P.DeterminantReindex
