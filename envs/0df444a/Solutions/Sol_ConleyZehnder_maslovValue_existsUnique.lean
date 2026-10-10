-- Prove2me | solution 1 for ConleyZehnder.maslovValue_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:50:36.219704+00:00
-- url     : https://prove2.me/submissions/d12a7cd9-de3d-4b10-b0cb-240d156daa40

import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_rhoHat_path_continuous

open ConleyZehnder Matrix

namespace CZ9

variable {n : ℕ}

theorem rhoHat_one : rhoHat (1 : Mat n) = 1 := by
  have hC : complexLinearPart (1 : Mat n) = 1 := by
    unfold complexLinearPart
    rw [Matrix.mul_one, Matrix.J_squared, sub_neg_eq_add, ← two_smul ℝ (1 : Mat n), smul_smul]
    norm_num
  have hD : complexLinearDet (1 : Mat n) = 1 := by
    unfold complexLinearDet
    rw [hC, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]
    have h1 : (Matrix.of fun i j => (1 : Mat n) (Sum.inl i) (Sum.inl j)).map
        (fun x : ℝ => (x : ℂ)) = 1 := by
      ext i j; by_cases h : i = j <;> simp [h, one_apply]
    have h2 : (Matrix.of fun i j => (1 : Mat n) (Sum.inr i) (Sum.inl j)).map
        (fun x : ℝ => (x : ℂ)) = 0 := by
      ext i j; simp [one_apply]
    rw [h1, h2, smul_zero, add_zero, det_one]
  simp [rhoHat, hD]

/-- A continuous argument of `ρ̂ ∘ φ` along a loop at `Id` has increment in `2πℤ`. -/
theorem integral (φ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ)
    (θ : unitInterval → ℝ) (h : IsArgLift (fun t => rhoHat (φ t)) θ) :
    ∃ k : ℤ, θ 1 - θ 0 = 2 * Real.pi * k := by
  have a0 : Complex.exp ((θ 0 : ℂ) * Complex.I) = 1 := by
    rw [← h.2 0]; simp only [hφ.2.1, rhoHat_one]
  have a1 : Complex.exp ((θ 1 : ℂ) * Complex.I) = 1 := by
    rw [← h.2 1]; simp only [hφ.2.2, rhoHat_one]
  have hS : Complex.exp (((θ 1 - θ 0 : ℝ) : ℂ) * Complex.I) = 1 := by
    have : ((θ 1 - θ 0 : ℝ) : ℂ) * Complex.I =
        (θ 1 : ℂ) * Complex.I - (θ 0 : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_sub, a0, a1, div_one]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hS
  refine ⟨k, ?_⟩
  have := congrArg Complex.im hk
  simpa [Complex.mul_im, mul_comm, mul_left_comm, mul_assoc] using this

end CZ9

theorem solution {n : ℕ} (φ : C(unitInterval, Mat n))
    (hφ : IsSymplecticLoop φ) : ∃! k : ℤ, IsMaslovValue φ k := by
  obtain ⟨hc, hn⟩ := rhoHat_path_continuous φ hφ.1
  obtain ⟨⟨θ, hθ⟩, u⟩ := argLift_exists_increment_unique hc hn
  obtain ⟨k, hk⟩ := CZ9.integral φ hφ θ hθ
  refine ⟨k, ⟨θ, hθ, hk⟩, ?_⟩
  rintro k' ⟨θ', hθ', hk'⟩
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have : (2 * Real.pi) * (k' : ℝ) = (2 * Real.pi) * k := by rw [← hk', ← hk, u θ θ' hθ hθ']
  exact_mod_cast (mul_left_cancel₀ hpi this)
