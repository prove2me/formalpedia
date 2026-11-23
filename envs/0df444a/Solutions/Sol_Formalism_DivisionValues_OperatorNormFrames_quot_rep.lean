-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.quot_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:24.997317+00:00
-- url     : https://prove2.me/submissions/0bd53ff4-415e-4d51-bcbc-b7552318609e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_nonneg
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_sq_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {n D : ℕ} (Hc X0 : Matrix (Fin n) (Fin n) ℂ) (h0 : IsUnit X0.det)
    (hH : (X0⁻¹)ᴴ * X0⁻¹ = Hc) (Pc : Matrix (Fin D) (Fin n) ℂ) (XQ : Matrix (Fin D) (Fin D) ℂ)
    (hQ : IsUnit XQ.det) (hG : (XQ⁻¹)ᴴ * XQ⁻¹ = (Pc * Hc⁻¹ * Pcᴴ)⁻¹) (y : Fin D → ℂ) :
    ∃ x : Fin n → ℂ, Pc.mulVec x = y ∧ fnorm X0 x = fnorm XQ y ∧
      ∀ u : Fin n → ℂ, Pc.mulVec u = 0 → fmaj X0 x u = 0 := by
  generalize hM : Pc * Hc⁻¹ * Pcᴴ = M at hG
  have hX0i : IsUnit (X0⁻¹).det := Matrix.isUnit_nonsing_inv_det X0 h0
  have hXQi : IsUnit (XQ⁻¹).det := Matrix.isUnit_nonsing_inv_det XQ hQ
  have hHcU : IsUnit Hc.det := by
    rw [isUnit_iff_ne_zero] at hX0i ⊢
    rw [← hH, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (star_ne_zero.2 hX0i) hX0i
  have hMiU : IsUnit (M⁻¹).det := by
    rw [isUnit_iff_ne_zero] at hXQi ⊢
    rw [← hG, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (star_ne_zero.2 hXQi) hXQi
  have hMU : IsUnit M.det := Matrix.isUnit_nonsing_inv_det_iff.mp hMiU
  have hHcH : Hcᴴ = Hc := by
    rw [← hH, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hHiH : (Hc⁻¹)ᴴ = Hc⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hHcH]
  have hMH : Mᴴ = M := by
    rw [← hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hHiH, Matrix.mul_assoc]
  have hGH : (M⁻¹)ᴴ = M⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hMH]
  have hx : Hc⁻¹ *ᵥ (Pcᴴ *ᵥ (M⁻¹ *ᵥ y)) = (Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hNN : (X0⁻¹ * (Hc⁻¹ * Pcᴴ * M⁻¹))ᴴ * (X0⁻¹ * (Hc⁻¹ * Pcᴴ * M⁻¹)) = (XQ⁻¹)ᴴ * XQ⁻¹ := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (X0⁻¹)ᴴ X0⁻¹, hH,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHiH, hGH]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hHcU]
    rw [← Matrix.mul_assoc Pc, ← Matrix.mul_assoc (Pc * Hc⁻¹), hM, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hMU, Matrix.one_mul]
  have hA : (X0⁻¹ * (Hc⁻¹ * Pcᴴ * M⁻¹))ᴴ * X0⁻¹ = M⁻¹ * Pc := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hH, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHiH, hGH]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHcU, Matrix.mul_one]
  refine ⟨Hc⁻¹ *ᵥ (Pcᴴ *ᵥ (M⁻¹ *ᵥ y)), ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM,
      Matrix.mul_nonsing_inv _ hMU, Matrix.one_mulVec]
  · rw [hx]
    have h1 : ((fnorm X0 ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y) ^ 2 : ℝ) : ℂ) = ((fnorm XQ y ^ 2 : ℝ) : ℂ) := by
      show ((Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y)) ^ 2 : ℝ) : ℂ) =
        ((Formalism.HermitianLatticesTheory.cnorm (XQ⁻¹ *ᵥ y) ^ 2 : ℝ) : ℂ)
      rw [Matrix.mulVec_mulVec, cnorm_sq_mulVec, cnorm_sq_mulVec, hNN]
    have h2 := Complex.ofReal_injective h1
    have ha : 0 ≤ fnorm X0 ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y) := cnorm_nonneg _
    have hb : 0 ≤ fnorm XQ y := cnorm_nonneg _
    exact le_antisymm (by nlinarith) (by nlinarith)
  · intro u hu
    rw [hx]
    show star (X0⁻¹ *ᵥ ((Hc⁻¹ * Pcᴴ * M⁻¹) *ᵥ y)) ⬝ᵥ (X0⁻¹ *ᵥ u) = 0
    rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hA, ← Matrix.mulVec_mulVec, hu]
    simp
end Formalism.DivisionValues.OperatorNormFrames
