-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.block3_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:26:04.680916+00:00
-- url     : https://prove2.me/submissions/4587db6d-e8db-41fe-8a55-558cfa13a86a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_apply

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
    (h : blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 = blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33) :
    A11 = ToralGalois ∧ A12 = cocyclesToWachVectorsExponent ∧ A13 = B13 ∧ A21 = B21 ∧ A22 = B22 ∧ A23 = B23 ∧ A31 = B31 ∧ A32 = B32 ∧ A33 = B33 := by
  have e : ∀ x y, blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 (eB k j ρ x) (eB k j ρ y) := fun x y => by rw [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext a b
  · simpa [block3_apply] using e (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b))
  · simpa [block3_apply] using e (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inr b))
  · simpa [block3_apply] using e (Sum.inl (Sum.inl a)) (Sum.inr b)
  · simpa [block3_apply] using e (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inl b))
  · simpa [block3_apply] using e (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inr b))
  · simpa [block3_apply] using e (Sum.inl (Sum.inr a)) (Sum.inr b)
  · simpa [block3_apply] using e (Sum.inr a) (Sum.inl (Sum.inl b))
  · simpa [block3_apply] using e (Sum.inr a) (Sum.inl (Sum.inr b))
  · simpa [block3_apply] using e (Sum.inr a) (Sum.inr b)
end Formalism.FourierDecayAlt.P.Ux2
