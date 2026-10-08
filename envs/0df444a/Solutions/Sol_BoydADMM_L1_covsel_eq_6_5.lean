-- Prove2me | solution 1 for BoydADMM.L1.covsel_eq_6_5
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T07:41:03.617996+00:00
-- url     : https://prove2.me/submissions/85ab27fe-df30-4f6d-8a1c-689fc2ed40ae

import Definitions.Def_BoydADMM_L1_CovSel
set_option autoImplicit false
section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1
 theorem scalar_root (ρ μ : ℝ) (hρ : 0 < ρ) :
    0 < covselRoot ρ μ ∧ ρ * covselRoot ρ μ - 1 / covselRoot ρ μ = μ := by
  have hd : 0 ≤ μ ^ 2 + 4 * ρ := by positivity
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg (μ ^ 2 + 4 * ρ)
  have hp : 0 < μ + Real.sqrt (μ ^ 2 + 4 * ρ) := by
    nlinarith [sq_nonneg (μ + Real.sqrt (μ ^ 2 + 4 * ρ))]
  have ht : 0 < covselRoot ρ μ := div_pos hp (by positivity)
  refine ⟨ht, ?_⟩
  have he : ρ * (covselRoot ρ μ) ^ 2 - μ * covselRoot ρ μ - 1 = 0 := by
    unfold covselRoot
    field_simp
    simp only [mul_comm ρ 4] at *
    nlinarith
  apply (mul_right_cancel₀ (ne_of_gt ht))
  field_simp
  nlinarith [he]
end ADMMCodex

end

section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
open BoydADMM.L1
 theorem spectral_update {n : ℕ} (S Z U Q : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (μ : Fin n → ℝ) (hρ : 0 < ρ) (hQ₁ : Qᵀ * Q = 1) (hQ₂ : Q * Qᵀ = 1)
    (hdecomp : ρ • (Z - U) - S = Q * diagonal μ * Qᵀ) :
    (covselX ρ Q μ).PosDef ∧ ρ • covselX ρ Q μ - (covselX ρ Q μ)⁻¹ =
      ρ • (Z - U) - S := by
  let r : Fin n → ℝ := fun i => covselRoot ρ (μ i)
  have hr : ∀ i, 0 < r i := fun i => (scalar_root ρ (μ i) hρ).1
  have hj : Function.Injective (fun v : Fin n → ℝ => v ᵥ* Q) := by
    intro x y h
    have := congrArg (fun v => v ᵥ* Qᵀ) h
    simpa only [vecMul_vecMul, hQ₂, vecMul_one] using this
  have hp : (covselX ρ Q μ).PosDef := by
    have hd := (posDef_diagonal_iff.mpr hr).mul_mul_conjTranspose_same hj
    simpa [covselX, r] using hd
  have hi : (covselX ρ Q μ)⁻¹ = Q * diagonal (fun i => (r i)⁻¹) * Qᵀ := by
    apply inv_eq_right_inv
    change (Q * diagonal r * Qᵀ) * (Q * diagonal (fun i => (r i)⁻¹) * Qᵀ) = 1
    calc
      _ = Q * (diagonal r * (Qᵀ * Q) * diagonal (fun i => (r i)⁻¹)) * Qᵀ := by simp only [Matrix.mul_assoc]
      _ = Q * diagonal (fun _ => (1 : ℝ)) * Qᵀ := by
        rw [hQ₁, Matrix.mul_one, diagonal_mul_diagonal]
        have hd : (fun i => r i * (r i)⁻¹) = (fun _ => (1 : ℝ)) := by
          funext i
          exact mul_inv_cancel₀ (ne_of_gt (hr i))
        rw [hd]
      _ = 1 := by simpa only [diagonal_one, Matrix.mul_one] using hQ₂
  refine ⟨hp, ?_⟩
  rw [hi, hdecomp]
  change ρ • (Q * diagonal r * Qᵀ) - Q * diagonal (fun i => (r i)⁻¹) * Qᵀ = _
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 1
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simpa [r, one_div] using (scalar_root ρ (μ i) hρ).2
  · simp [diagonal_apply, h]
end ADMMCodex

end

set_option autoImplicit false
open Matrix BoydADMM.L1
theorem solution {n : ℕ} (S Z U Q : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (μ : Fin n → ℝ)
    (hρ : 0 < ρ) (hQ₁ : Qᵀ * Q = 1) (hQ₂ : Q * Qᵀ = 1)
    (hdecomp : ρ • (Z - U) - S = Q * Matrix.diagonal μ * Qᵀ) :
    (covselX ρ Q μ).PosDef ∧ ρ • covselX ρ Q μ - (covselX ρ Q μ)⁻¹ = ρ • (Z - U) - S := by
  exact ADMMCodex.spectral_update S Z U Q ρ μ hρ hQ₁ hQ₂ hdecomp



#print axioms solution
