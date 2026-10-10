-- Prove2me | solution 1 for ConleyZehnder.czIndex_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:54:37.023192+00:00
-- url     : https://prove2.me/submissions/c473e0ec-6699-4ec8-a19e-fbf61662b523

import Theorems.Thm_ConleyZehnder_czValue_existsUnique
import Theorems.Thm_ConleyZehnder_czIndex_naturality

open ConleyZehnder Matrix

namespace CZ18

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

theorem czIndex_eq_of_isCZValue (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) {k : ℤ}
    (hk : IsCZValue ψ k) : czIndex ψ = k := by
  have hex : ∃ k, IsCZValue ψ k := ⟨k, hk⟩
  unfold czIndex
  rw [dif_pos hex]
  exact (czValue_existsUnique ψ hψ).unique hex.choose_spec hk

theorem transpose_mem_SP (ψ ψtr : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n)
    (htr : ∀ t, ψtr t = (ψ t).transpose) : ψtr ∈ SP n := by
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [htr]; exact SymplecticGroup.transpose_mem (hψ.1 t)
  · rw [htr, hψ.2.1, transpose_one]
  · rw [htr, ← transpose_one, ← transpose_sub, det_transpose]; exact hψ.2.2

theorem isCZValue_transpose (ψ ψtr : C(unitInterval, Mat n))
    (htr : ∀ t, ψtr t = (ψ t).transpose) {k : ℤ} (hk : IsCZValue ψ k) :
    IsCZValue ψtr (-k) := by
  obtain ⟨χ, ⟨h0, hS, h1⟩, θ₁, θ₂, hθ₁, hθ₂, hsum⟩ := hk
  let χ' : C(unitInterval, Mat n) := ⟨fun t => (χ t)ᵀ, χ.continuous.matrix_transpose⟩
  refine ⟨χ', ⟨?_, fun t => ?_, ?_⟩, fun t => -θ₁ t, fun t => -θ₂ t, ⟨hθ₁.1.neg, fun t => ?_⟩,
    ⟨hθ₂.1.neg, fun t => ?_⟩, ?_⟩
  · show (χ 0)ᵀ = ψtr 1
    rw [htr, h0]
  · refine ⟨SymplecticGroup.transpose_mem (hS t).1, ?_⟩
    show (1 - (χ t)ᵀ).det ≠ 0
    rw [← transpose_one, ← transpose_sub, det_transpose]; exact (hS t).2
  · show (χ 1)ᵀ = Wplus n ∨ (χ 1)ᵀ = Wminus n
    rcases h1 with h | h
    · left; rw [h, Wplus, transpose_neg, transpose_one]
    · right; rw [h, Wminus, diagonal_transpose]
  · show rhoHat (ψtr t) = _
    rw [htr, rhoHat_transpose, show rhoHat (ψ t) = _ from hθ₁.2 t, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  · show rhoHat (χ t)ᵀ = _
    rw [rhoHat_transpose, show rhoHat (χ t) = _ from hθ₂.2 t, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  · push_cast
    linarith

end CZ18

open CZ18 in
theorem solution {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n)
    (ψinv ψtr : C(unitInterval, Mat n)) (hinv : ∀ t, ψinv t = (ψ t)⁻¹)
    (htr : ∀ t, ψtr t = (ψ t).transpose) :
    czIndex ψinv = -czIndex ψ ∧ czIndex ψtr = -czIndex ψ := by
  obtain ⟨k, hk, -⟩ := czValue_existsUnique ψ hψ
  have hψk : czIndex ψ = k := czIndex_eq_of_isCZValue ψ hψ hk
  have htrSP := transpose_mem_SP ψ ψtr hψ htr
  have htrk : czIndex ψtr = -czIndex ψ := by
    rw [hψk]; exact czIndex_eq_of_isCZValue ψtr htrSP (isCZValue_transpose ψ ψtr htr hk)
  refine ⟨?_, htrk⟩
  rw [← htrk]
  refine czIndex_naturality (ContinuousMap.const _ (J₀ n)) (fun _ => SymplecticGroup.J_mem _ _)
    ψtr htrSP ψinv (fun t => ?_)
  show ψinv t = J₀ n * ψtr t * (J₀ n)⁻¹
  rw [hinv, htr, show J₀ n = Matrix.J (Fin n) ℝ from rfl, J_inv,
    SymplecticGroup.inv_eq_symplectic_inv _ (hψ.1 t)]
  simp only [Matrix.mul_neg, Matrix.neg_mul]
