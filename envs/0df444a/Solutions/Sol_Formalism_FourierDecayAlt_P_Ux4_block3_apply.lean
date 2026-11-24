-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.block3_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:51:30.53866+00:00
-- url     : https://prove2.me/submissions/fc6b7d26-45a8-4511-840c-979e4fb1e466

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (x y : Ix k j ρ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23) (Matrix.fromCols A31 A32) A33 x y := by
  simp [blk3, Matrix.reindex_apply]
end Formalism.FourierDecayAlt.P.Ux4
