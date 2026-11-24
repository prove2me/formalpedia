-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantReindex.sign_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:12.254268+00:00
-- url     : https://prove2.me/submissions/2d86abce-0bfd-4705-b41a-65baa4a4ee46

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
    ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 ∨ ((Equiv.Perm.sign τ : ℤ) : ℂ) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp
end Formalism.FourierDecayAlt.P.DeterminantReindex
