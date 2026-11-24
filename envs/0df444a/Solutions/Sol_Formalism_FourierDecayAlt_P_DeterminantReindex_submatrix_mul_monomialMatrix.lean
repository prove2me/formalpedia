-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantReindex.submatrix_mul_monomialMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:12.9573+00:00
-- url     : https://prove2.me/submissions/2d226b5b-ec3f-43df-a39e-27272062ae4b

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
theorem _root_.solution {m k : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ)
    (e f : Fin k → Fin m) :
    (M * C2.monoP w d).submatrix e f = M.submatrix e (fun s => w (f s)) * Matrix.diagonal (fun s => d (f s)) := by
  ext t s
  rw [Matrix.mul_diagonal]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, C2.monoP, Matrix.of_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end Formalism.FourierDecayAlt.P.DeterminantReindex
