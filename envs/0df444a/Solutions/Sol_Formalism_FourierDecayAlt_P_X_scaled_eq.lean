-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.X.scaled_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:07.375209+00:00
-- url     : https://prove2.me/submissions/f5a3e481-487e-45bd-8f68-aa4eba5e8497

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalingExponentIdentities

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
open Formalism.FourierDecayAlt.P.X
namespace Formalism.FourierDecayAlt.P.X
theorem _root_.solution {K : Type} [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (κ : K) (l : ℕ)
    (hl : l ≤ n) :
    (Matrix.of (fun a b : Fin n => κ ^ ((a : ℕ) + (b : ℕ)) * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun a : Fin l => κ ^ (a : ℕ)) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun a : Fin l => κ ^ (a : ℕ)) := by
  ext a b
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, pow_add]
  ring
end Formalism.FourierDecayAlt.P.X
