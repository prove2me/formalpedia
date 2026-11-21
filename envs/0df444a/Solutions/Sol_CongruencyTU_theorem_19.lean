-- Prove2me | solution 1 for CongruencyTU.theorem_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:41:10.072187+00:00
-- url     : https://prove2.me/submissions/bc4370b7-f467-4bce-aa1e-592c3f92264c

import Mathlib

open Matrix

namespace Aux_CongruencyTU_theorem_19

lemma mv {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (v : n → ℝ) (i : m) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

end Aux_CongruencyTU_theorem_19

open Aux_CongruencyTU_theorem_19 in
theorem solution {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℤ) (a₁ : Fin k → ℤ) (a₂ : Fin n → ℤ)
    (α : ℤ)
    (hTU : (fromBlocks A (replicateCol (Fin 1) a₁) (replicateRow (Fin 1) a₂) !![α]).IsTotallyUnimodular)
    (hα : α ≠ 0) :
    (A - α • vecMulVec a₁ a₂).IsTotallyUnimodular ∧
    ∀ (b : Fin k → ℝ) (β : ℝ) (x : Fin n → ℝ) (y : ℝ),
      ((A.map (Int.cast : ℤ → ℝ)) *ᵥ x + y • (fun i => (a₁ i : ℝ)) ≤ b ∧
          (fun j => (a₂ j : ℝ)) ⬝ᵥ x + (α : ℝ) * y = β) ↔
        (((A - α • vecMulVec a₁ a₂).map (Int.cast : ℤ → ℝ)) *ᵥ x ≤
            b - ((α : ℝ) * β) • (fun i => (a₁ i : ℝ)) ∧
          y = (α : ℝ) * β - (α : ℝ) * ((fun j => (a₂ j : ℝ)) ⬝ᵥ x)) := by
  have hα_range : α ∈ Set.range SignType.cast := by
    have := hTU.apply (Sum.inr 0) (Sum.inr 0)
    simpa using this
  have hαα : α * α = 1 := by
    obtain ⟨t, ht⟩ := hα_range
    subst ht
    cases t <;> simp_all
  refine ⟨?_, ?_⟩
  · rw [Matrix.isTotallyUnimodular_iff]
    intro t f g
    have hbig := (Matrix.isTotallyUnimodular_iff_fintype _).mp hTU (Fin t ⊕ Fin 1)
      (Sum.map f id) (Sum.map g id)
    have hsub : (fromBlocks A (replicateCol (Fin 1) a₁) (replicateRow (Fin 1) a₂) !![α]).submatrix
        (Sum.map f id) (Sum.map g id) =
        fromBlocks (A.submatrix f g) (replicateCol (Fin 1) (a₁ ∘ f))
          (replicateRow (Fin 1) (a₂ ∘ g)) !![α] := by
      ext (i | i) (j | j) <;> simp
    rw [hsub] at hbig
    have hDD : (!![α] : Matrix (Fin 1) (Fin 1) ℤ) * !![α] = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, hαα]
    letI : Invertible (!![α] : Matrix (Fin 1) (Fin 1) ℤ) := ⟨!![α], hDD, hDD⟩
    have hBC : replicateCol (Fin 1) (a₁ ∘ f) * ⅟(!![α] : Matrix (Fin 1) (Fin 1) ℤ) *
        replicateRow (Fin 1) (a₂ ∘ g) = α • vecMulVec (a₁ ∘ f) (a₂ ∘ g) := by
      show replicateCol (Fin 1) (a₁ ∘ f) * (!![α] : Matrix (Fin 1) (Fin 1) ℤ) *
        replicateRow (Fin 1) (a₂ ∘ g) = α • vecMulVec (a₁ ∘ f) (a₂ ∘ g)
      ext i j
      first
        | (simp [Matrix.mul_apply, Matrix.vecMulVec_apply]; done)
        | (simp [Matrix.mul_apply, Matrix.vecMulVec_apply]; ring)
    rw [Matrix.det_fromBlocks₂₂, Matrix.det_fin_one_of, hBC] at hbig
    have hN : (A - α • vecMulVec a₁ a₂).submatrix f g =
        A.submatrix f g - α • vecMulVec (a₁ ∘ f) (a₂ ∘ g) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, Function.comp_apply, smul_eq_mul]
    rw [hN]
    obtain ⟨s, hs⟩ := hbig
    obtain ⟨u, hu⟩ := hα_range
    refine ⟨u * s, ?_⟩
    rw [SignType.coe_mul, hu, hs, ← mul_assoc, hαα, one_mul]
  · intro b β x y
    have hα2 : (α : ℝ) * α = 1 := by exact_mod_cast hαα
    have hrow : ∀ i, (((A - α • vecMulVec a₁ a₂).map (Int.cast : ℤ → ℝ)) *ᵥ x) i =
        ((A.map (Int.cast : ℤ → ℝ)) *ᵥ x) i -
          (α : ℝ) * (a₁ i : ℝ) * ((fun j => (a₂ j : ℝ)) ⬝ᵥ x) := by
      intro i
      rw [mv, mv]
      simp only [dotProduct, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hrow]
    constructor
    · rintro ⟨h1, h2⟩
      have hy : y = (α : ℝ) * β - (α : ℝ) * ((fun j => (a₂ j : ℝ)) ⬝ᵥ x) := by
        linear_combination (α : ℝ) * h2 - y * hα2
      refine ⟨fun i => ?_, hy⟩
      have := h1 i
      rw [hy] at this
      linarith
    · rintro ⟨h1, hy⟩
      refine ⟨fun i => ?_, ?_⟩
      · have := h1 i
        rw [hy]
        linarith
      · rw [hy]
        linear_combination (β - (fun j => (a₂ j : ℝ)) ⬝ᵥ x) * hα2
