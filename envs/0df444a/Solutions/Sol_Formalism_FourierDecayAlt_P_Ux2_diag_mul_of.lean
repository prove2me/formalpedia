-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.diag_mul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:59.844696+00:00
-- url     : https://prove2.me/submissions/e2574d63-a0e0-4c6c-84af-99a3bdbe0aa6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_GlobalTheory_TriangularDiagonal_mul_diag_of_triangular


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
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {κ : Fin p → ℤ} (hκ : Function.Injective κ) {M N : Matrix (Fin p) (Fin p) ℂ}
    (hM : ∀ a b, κ a < κ b → M a b = 0) (hN : ∀ a b, κ a < κ b → N a b = 0) (i : Fin p) :
    (M * N) i i = M i i * N i i := by
  first | exact GlobalTheory.TriangularDiagonal.mul_diag_of_triangular .. | (apply GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> assumption) | (intros; apply GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> assumption) | (apply @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> assumption) | (intros; apply @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> assumption) | (apply @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> first | assumption | infer_instance) | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M N hM hN i | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M N hM hN | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M N hM | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M N | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p
end Formalism.FourierDecayAlt.P.Ux2
