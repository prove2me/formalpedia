-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.frame_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:40:56.918899+00:00
-- url     : https://prove2.me/submissions/b29b0f95-c8bd-4f5d-ab26-2e02dd5b2ab6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_H_Ep
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_Ep_H
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_posDef_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (F : Frame H Ep Em) (Y : Matrix m Q ℂ) (hY : (Tm H Y).PosDef) :
    ∃ g ∈ UH H, ∃ a : Matrix Q Q ℂ, IsUnit a.det ∧ Y = g * Em * a := by
  obtain ⟨a, ha, hTa⟩ := posDef_factor hY
  have ha' : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  set Y₀ : Matrix m Q ℂ := Y * a⁻¹ with hY₀
  have hYHY : Yᴴ * H * Y = -(aᴴ * a) := by
    rw [← hTa]; unfold Tm; simp
  have h1 : Y₀ᴴ * H * Y₀ = -1 := by
    rw [hY₀, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    have : aᴴ⁻¹ * Yᴴ * H * (Y * a⁻¹) = aᴴ⁻¹ * (Yᴴ * H * Y) * a⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, hYHY, Matrix.mul_neg, Matrix.neg_mul]
    have : aᴴ⁻¹ * (aᴴ * a) * a⁻¹ = (aᴴ⁻¹ * aᴴ) * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_nonsing_inv _ ha, Matrix.nonsing_inv_mul _ ha']; simp
  set b : Matrix P Q ℂ := Epᴴ * Y₀ with hb
  have hbH : bᴴ = Y₀ᴴ * Ep := by rw [hb, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hS : (1 + b * bᴴ).PosDef := Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_self_mul_conjTranspose b)
  obtain ⟨β, hβ, hSβ⟩ := posDef_factor hS
  have hβ' : IsUnit βᴴ.det := by rw [Matrix.det_conjTranspose]; exact hβ.star
  set Z₁ : Matrix m P ℂ := Ep + Y₀ * bᴴ with hZ₁
  have h2 : Y₀ᴴ * H * Z₁ = 0 := by
    rw [hZ₁, Matrix.mul_add, Matrix.mul_assoc, F.H_Ep, ← Matrix.mul_assoc, h1, ← hbH]; simp
  have h3 : Z₁ᴴ * H * Z₁ = 1 + b * bᴴ := by
    have e1 : Z₁ᴴ = Epᴴ + b * Y₀ᴴ := by
      rw [hZ₁, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [e1, Matrix.add_mul, Matrix.add_mul, F.Ep_H]
    have e2 : b * Y₀ᴴ * H * Z₁ = b * (Y₀ᴴ * H * Z₁) := by simp only [Matrix.mul_assoc]
    rw [e2, h2, Matrix.mul_zero, add_zero, hZ₁, Matrix.mul_add, F.pp, ← Matrix.mul_assoc, ← hb]
  set Z : Matrix m P ℂ := Z₁ * β⁻¹ with hZ
  have h4 : Y₀ᴴ * H * Z = 0 := by
    rw [hZ, ← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have h5 : Zᴴ * H * Y₀ = 0 := by
    have := congrArg Matrix.conjTranspose h4
    simpa [Matrix.conjTranspose_mul, F.herm, Matrix.mul_assoc] using this
  have h6 : Zᴴ * H * Z = 1 := by
    rw [hZ, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    have : βᴴ⁻¹ * Z₁ᴴ * H * (Z₁ * β⁻¹) = βᴴ⁻¹ * (Z₁ᴴ * H * Z₁) * β⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, h3, hSβ]
    have : βᴴ⁻¹ * (βᴴ * β) * β⁻¹ = (βᴴ⁻¹ * βᴴ) * (β * β⁻¹) := by simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_nonsing_inv _ hβ, Matrix.nonsing_inv_mul _ hβ']; simp
  refine ⟨Y₀ * Emᴴ + Z * Epᴴ, ?_, a, ha, ?_⟩
  · show (Y₀ * Emᴴ + Z * Epᴴ)ᴴ * H * (Y₀ * Emᴴ + Z * Epᴴ) = H
    have : (Y₀ * Emᴴ + Z * Epᴴ)ᴴ * H * (Y₀ * Emᴴ + Z * Epᴴ) =
        Em * (Y₀ᴴ * H * Y₀) * Emᴴ + Em * (Y₀ᴴ * H * Z) * Epᴴ + Ep * (Zᴴ * H * Y₀) * Emᴴ +
          Ep * (Zᴴ * H * Z) * Epᴴ := by
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [this, h1, h4, h5, h6, ← F.diff]
    simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    abel
  · rw [Matrix.add_mul, Matrix.mul_assoc Y₀, F.mm, Matrix.mul_assoc Z, F.pm, Matrix.mul_zero, add_zero, Matrix.mul_one,
      hY₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
