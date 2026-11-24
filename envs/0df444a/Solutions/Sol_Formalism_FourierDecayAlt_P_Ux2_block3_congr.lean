-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.block3_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:54.810687+00:00
-- url     : https://prove2.me/submissions/001b50f4-e562-4cdc-916b-d3bc9407cd49

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {A11 ToralGalois : Matrix (Fin j) (Fin j) ℂ} {A12 cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 B13 : Matrix (Fin j) (Fin j) ℂ} {A21 B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 B22 : B.Mat k ρ}
    {A23 B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 B31 : Matrix (Fin j) (Fin j) ℂ}
    {A32 B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 B33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : A11 = ToralGalois) (h12 : A12 = cocyclesToWachVectorsExponent) (h13 : A13 = B13) (h21 : A21 = B21) (h22 : A22 = B22) (h23 : A23 = B23)
    (h31 : A31 = B31) (h32 : A32 = B32) (h33 : A33 = B33) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 = blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 := by
  subst_vars; rfl
end Formalism.FourierDecayAlt.P.Ux2
