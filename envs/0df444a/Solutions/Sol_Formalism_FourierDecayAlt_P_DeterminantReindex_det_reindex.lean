-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantReindex.det_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:44.691354+00:00
-- url     : https://prove2.me/submissions/5df27414-cbeb-4f7c-8031-ea31d40c277b

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
theorem _root_.solution {m k : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (e ρ f : Fin k → Fin m) (τ : Equiv.Perm (Fin k))
    (h : ∀ t, e t = ρ (τ t)) :
    (M.submatrix e f).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (M.submatrix ρ f).det := by
  have : M.submatrix e f = (M.submatrix ρ f).submatrix τ id := by
    ext t s; simp [h]
  rw [this, Matrix.det_permute]
end Formalism.FourierDecayAlt.P.DeterminantReindex
