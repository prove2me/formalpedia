-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.block3_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:25:57.820295+00:00
-- url     : https://prove2.me/submissions/29c92dfd-74ea-4602-8dde-bffb40b4d406

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 (k := k) (j := j) (ρ := ρ) A11 A12 A13 A21 A22 A23 A31 A32 A33 = blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 ↔
      A11 = ToralGalois ∧ A12 = cocyclesToWachVectorsExponent ∧ A13 = B13 ∧ A21 = B21 ∧ A22 = B22 ∧ A23 = B23 ∧ A31 = B31 ∧ A32 = B32 ∧ A33 = B33 := by
  constructor
  · intro h
    have e : ∀ x y : Ix k j ρ, Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23)
        (Matrix.fromCols A31 A32) A33 x y = Matrix.fromBlocks (Matrix.fromBlocks ToralGalois cocyclesToWachVectorsExponent B21 B22) (Matrix.fromRows B13 B23)
        (Matrix.fromCols B31 B32) B33 x y := by
      intro x y
      rw [← block3_apply, ← block3_apply, h]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext a b
    · simpa using e (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b))
    · simpa using e (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inr b))
    · simpa [Matrix.fromRows_apply_inl] using e (Sum.inl (Sum.inl a)) (Sum.inr b)
    · simpa using e (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inl b))
    · simpa using e (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inr b))
    · simpa [Matrix.fromRows_apply_inr] using e (Sum.inl (Sum.inr a)) (Sum.inr b)
    · simpa [Matrix.fromCols_apply_inl] using e (Sum.inr a) (Sum.inl (Sum.inl b))
    · simpa [Matrix.fromCols_apply_inr] using e (Sum.inr a) (Sum.inl (Sum.inr b))
    · simpa using e (Sum.inr a) (Sum.inr b)
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl
end Formalism.FourierDecayAlt.P.Ux3
