-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.det_submatrix_unitriangular_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:44:01.266566+00:00
-- url     : https://prove2.me/submissions/2a735c28-42e0-4561-8c48-ae2f3bac3ab8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetSubmatrixUnitriangularEqOne

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
open C2x2 CardInsertEmbedding DeterminantReindex
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m k : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) (hu : u ∈ C2.UTset m) (e : Fin k → Fin m)
    (he : ∀ t, (e t).val = t.val) : (u.submatrix e e).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp only [Matrix.submatrix_apply, hu.2, Finset.prod_const_one]
  · intro t s h
    simp only [Matrix.submatrix_apply]
    apply hu.1
    rw [Fin.lt_def, he, he]
    exact h
end Formalism.FourierDecayAlt.P
