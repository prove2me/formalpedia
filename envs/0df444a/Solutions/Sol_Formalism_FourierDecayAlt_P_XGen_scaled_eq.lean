-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.XGen.scaled_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:50.516012+00:00
-- url     : https://prove2.me/submissions/33b8267d-bdec-46f0-a934-d2623a08825c

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinorScalingLawGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix
open Formalism.FourierDecayAlt.P.XGen
namespace Formalism.FourierDecayAlt.P.XGen
theorem _root_.solution {K : Type} [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (α β : Fin n → K)
    (l : ℕ) (hl : l ≤ n) :
    (Matrix.of (fun a b : Fin n => α a * β b * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun a : Fin l => α (Fin.castLE hl a)) *
          Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun a : Fin l => β (Fin.castLE hl a)) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring
end Formalism.FourierDecayAlt.P.XGen
