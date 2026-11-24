-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:24.853049+00:00
-- url     : https://prove2.me/submissions/e4674451-ab64-40de-92d5-2e3e6f2ce7a5

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution {P Q : Matrix l l ℂ} (hP : P.det ≠ 0) (S M : Matrix l l ℂ) (c : ℂ)
    (h : ∀ j k, ∑ a, P a j * M a k = c * Q k j) : ∑ j, ∑ k, S j k * M j k = c * (P⁻¹ * (S * Q)).trace := by
  have h1 : Pᵀ * M = c • Qᵀ := by
    ext j k
    simp [Matrix.mul_apply, h]
  have hu : IsUnit Pᵀ.det := by
    rw [det_transpose]
    exact hP.isUnit
  have h2 : M = Pᵀ⁻¹ * (c • Qᵀ) := by
    rw [← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have h3 : ∑ j, ∑ k, S j k * M j k = (S * Mᵀ).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h4 : S * (Pᵀ⁻¹ * (c • Qᵀ))ᵀ = c • (S * Q * P⁻¹) := by
    rw [transpose_mul, transpose_smul, transpose_transpose, transpose_nonsing_inv, transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
  rw [h3, h2, h4, trace_smul, smul_eq_mul, Matrix.trace_mul_comm]
end CompanionTheory.ThKR.Mp
