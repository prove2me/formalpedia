-- Prove2me | solution 1 for ConleyZehnder.spStar_rhoHat_increment_eq_zero_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:13:32.34984+00:00
-- url     : https://prove2.me/submissions/58d9534c-589c-48bc-99fd-0dd0276d8d6f

import Theorems.Thm_ConleyZehnder_spStar_rhoHat_lift_increment_eq

open ConleyZehnder Matrix

namespace CZ16B

variable {n : ℕ}

/-- `det_ℂ C_{Aᵀ} = conj (det_ℂ C_A)`. -/
theorem complexLinearDet_transpose (A : Mat n) :
    complexLinearDet Aᵀ = starRingEnd ℂ (complexLinearDet A) := by
  set M : Matrix (Fin n) (Fin n) ℂ :=
    (complexLinearPart A).toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
      Complex.I • (complexLinearPart A).toBlocks₂₁.map (fun x : ℝ => (x : ℂ)) with hM
  have h11 : ∀ i j, (complexLinearPart Aᵀ).toBlocks₁₁ i j = (complexLinearPart A).toBlocks₁₁ j i := by
    intro i j
    simp [complexLinearPart, toBlocks₁₁, Matrix.J, mul_apply, Fintype.sum_sum_type, fromBlocks, one_apply]
  have h21 : ∀ i j, (complexLinearPart Aᵀ).toBlocks₂₁ i j = -(complexLinearPart A).toBlocks₂₁ j i := by
    intro i j
    simp [complexLinearPart, toBlocks₂₁, Matrix.J, mul_apply, Fintype.sum_sum_type, fromBlocks, one_apply]
    ring
  have hT : (complexLinearPart Aᵀ).toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
      Complex.I • (complexLinearPart Aᵀ).toBlocks₂₁.map (fun x : ℝ => (x : ℂ)) = Mᴴ := by
    ext i j
    simp only [hM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, conjTranspose_apply,
      smul_eq_mul, h11, h21, star_add, star_mul', Complex.star_def, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast; ring
  unfold complexLinearDet
  rw [hT, det_conjTranspose]
  rfl

theorem rhoHat_transpose (A : Mat n) : rhoHat Aᵀ = starRingEnd ℂ (rhoHat A) := by
  unfold rhoHat
  rw [complexLinearDet_transpose, map_div₀, Complex.conj_ofReal, Complex.norm_conj]

end CZ16B

open CZ16B

/-- A path in `Sp*` between two symmetric matrices has zero `ρ̂`-argument increment. -/
theorem solution {n : ℕ} (χ : C(unitInterval, Mat n))
    (hχ : ∀ t, χ t ∈ SpStar n) (h0 : (χ 0)ᵀ = χ 0) (h1 : (χ 1)ᵀ = χ 1)
    (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (χ t)) θ) :
    θ 1 - θ 0 = 0 := by
  let χ' : C(unitInterval, Mat n) := ⟨fun t => (χ t)ᵀ, χ.continuous.matrix_transpose⟩
  have hχ' : ∀ t, χ' t ∈ SpStar n := fun t =>
    ⟨SymplecticGroup.transpose_mem (hχ t).1, by
      show (1 - (χ t)ᵀ).det ≠ 0
      rw [← transpose_one, ← transpose_sub, det_transpose]; exact (hχ t).2⟩
  have hθ' : IsArgLift (fun t => rhoHat (χ' t)) (fun t => -θ t) := ⟨hθ.1.neg, fun t => by
    show rhoHat (χ t)ᵀ = _
    rw [rhoHat_transpose, show rhoHat (χ t) = _ from hθ.2 t, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]⟩
  have := spStar_rhoHat_lift_increment_eq χ χ' hχ hχ' h0.symm h1.symm θ _ hθ hθ'
  linarith
