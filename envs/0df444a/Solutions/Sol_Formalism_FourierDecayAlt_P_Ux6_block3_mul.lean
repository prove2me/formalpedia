-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.block3_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:55:52.912817+00:00
-- url     : https://prove2.me/submissions/9d4a51b6-7ffb-4c60-aa3a-72af18c157d5

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 * blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 * ToralGalois + A12 * B21 + A13 * B31) (A11 * cocyclesToWachVectorsExponent + A12 * B22 + A13 * B32) (A11 * B13 + A12 * B23 + A13 * B33)
        (A21 * ToralGalois + A22 * B21 + A23 * B31) (A21 * cocyclesToWachVectorsExponent + A22 * B22 + A23 * B32) (A21 * B13 + A22 * B23 + A23 * B33)
        (A31 * ToralGalois + A32 * B21 + A33 * B31) (A31 * cocyclesToWachVectorsExponent + A32 * B22 + A33 * B32) (A31 * B13 + A32 * B23 + A33 * B33) := by
  unfold blk3
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.reindex_apply]
  congr 1
  ext (((a | a) | a)) (((b | b) | b)) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
end Formalism.FourierDecayAlt.P.Ux6
