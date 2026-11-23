-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.comm_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:27.928846+00:00
-- url     : https://prove2.me/submissions/5c063690-d63e-4c60-8aaa-704f9b0ed363

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_ext_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {n : ℕ} {H : Matrix (Fin n) (Fin n) K} (hHh : Hᴴ = H) (hHu : IsUnit H)
    {𝒯 : Set (Matrix (Fin n) (Fin n) K)} (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, Tᴴ * H = H * T')
    {Z : Submodule K (Fin n → K)} (hZ : IsCommStable 𝒯 Z) {e : Matrix (Fin n) (Fin n) K}
    (heH : eᴴ * H = H * e) (h1 : ∀ x, e *ᵥ x ∈ Z) (h2 : ∀ z ∈ Z, e *ᵥ z = z)
    (B : Matrix (Fin n) (Fin n) K) (hB : ∀ T ∈ 𝒯, B * T = T * B) : e * B = B * e := by
  obtain ⟨Hi, hH1, hH2⟩ : ∃ Hi : Matrix (Fin n) (Fin n) K, H * Hi = 1 ∧ Hi * H = 1 :=
    ⟨↑hHu.unit⁻¹, hHu.mul_val_inv, hHu.val_inv_mul⟩
  have R2 : ∀ X : Matrix (Fin n) (Fin n) K, Hi * (H * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hH2, Matrix.one_mul]
  have hHiH : Hiᴴ * H = 1 := by
    rw [← hHh, ← Matrix.conjTranspose_mul, hH1, Matrix.conjTranspose_one]
  have hB' : ∀ T ∈ 𝒯, Hi * (Bᴴ * H) * T = T * (Hi * (Bᴴ * H)) := by
    intro T hT
    obtain ⟨T', hT', hTT'⟩ := hadj T hT
    have hHT : H * T = T'ᴴ * H := by
      have := congrArg Matrix.conjTranspose hTT'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hHh] at this
      exact this
    have hBT' : Bᴴ * T'ᴴ = T'ᴴ * Bᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hB T' hT']
    have hiT : Hi * T'ᴴ = T * Hi := by
      calc Hi * T'ᴴ = Hi * T'ᴴ * (H * Hi) := by rw [hH1, Matrix.mul_one]
        _ = Hi * (T'ᴴ * H) * Hi := by simp only [Matrix.mul_assoc]
        _ = Hi * (H * T) * Hi := by rw [hHT]
        _ = T * Hi := by rw [← Matrix.mul_assoc Hi H T, hH2, Matrix.one_mul]
    calc Hi * (Bᴴ * H) * T = Hi * (Bᴴ * (H * T)) := by simp only [Matrix.mul_assoc]
      _ = Hi * (Bᴴ * T'ᴴ) * H := by rw [hHT]; simp only [Matrix.mul_assoc]
      _ = Hi * T'ᴴ * (Bᴴ * H) := by rw [hBT']; simp only [Matrix.mul_assoc]
      _ = T * (Hi * (Bᴴ * H)) := by rw [hiT]; simp only [Matrix.mul_assoc]
  have hadjB : (Hi * (Bᴴ * H))ᴴ * H = H * B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh,
      Matrix.mul_assoc, hHiH, Matrix.mul_one]
  have hproj : ∀ X : Matrix (Fin n) (Fin n) K, (∀ z ∈ Z, X *ᵥ z ∈ Z) → e * X * e = X * e :=
    fun X hX => ext_mulVec fun x => by
      have := h2 _ (hX _ (h1 x))
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at this ⊢
      exact this
  have hgen : ∀ X : Matrix (Fin n) (Fin n) K, Xᴴ * H = H * B → e * X * e = X * e →
      e * B * e = e * B := by
    intro X hX hXe
    have RheH : ∀ Y : Matrix (Fin n) (Fin n) K, eᴴ * (H * Y) = H * (e * Y) := fun Y => by
      rw [← Matrix.mul_assoc, heH, Matrix.mul_assoc]
    have RhX : ∀ Y : Matrix (Fin n) (Fin n) K, Xᴴ * (H * Y) = H * (B * Y) := fun Y => by
      rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc]
    have k1 : (e * X * e)ᴴ * H = H * (e * B * e) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, heH, RheH, RhX]
    have k2 : (X * e)ᴴ * H = H * (e * B) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hX, RheH]
    have k3 : H * (e * B * e) = H * (e * B) := by rw [← k1, ← k2, hXe]
    calc e * B * e = Hi * (H * (e * B * e)) := by rw [R2]
      _ = Hi * (H * (e * B)) := by rw [k3]
      _ = e * B := R2 _
  have hBe := hproj B fun z hz => hZ B hB z hz
  have hXe := hproj _ fun z hz => hZ _ hB' z hz
  exact (hgen _ hadjB hXe).symm.trans hBe
end Formalism.DivisionValues.FinitelyNonzeroLinear
