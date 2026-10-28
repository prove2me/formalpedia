-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:05.709981+00:00
-- url     : https://prove2.me/submissions/87d81e06-c13b-449b-975d-487979f98604

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

noncomputable section
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
section SubsetSum
variable {α : Type*} [DecidableEq α]
/-- The square of the norm of a finite sum is the double sum of inner products. -/
theorem FunctionalInequalities.Analysis.Tensor.norm_sq_sum_eq_sum_sum_inner {ι : Type*} (s : Finset ι) (x : ι → V) :
    ‖∑ i ∈ s, x i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, inner ℝ (x i) (x j) := by
    calc
      ‖∑ i ∈ s, x i‖ ^ 2 =
          inner ℝ (∑ i ∈ s, x i) (∑ i ∈ s, x i) := by
        exact (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i ∈ s, inner ℝ (x i) (∑ j ∈ s, x j) := by
        rw [sum_inner]
      _ = ∑ i ∈ s, ∑ j ∈ s, inner ℝ (x i) (x j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [inner_sum]
/-- Expanding squared norms of filtered sums: for a family `𝓔`, a finite index set `P` and a relation
`r`, `∑_{E ∈ 𝓔} ‖∑_{F ∈ P, r F E} x_F‖² = ∑_{F, F' ∈ P} #{E ∈ 𝓔 : r F E ∧ r F' E} ⟪x_F, x_F'⟫`. -/
theorem solution {β ι : Type*} (𝓔 : Finset β) (P : Finset ι) (r : ι → β → Prop)
    [∀ F E, Decidable (r F E)] (x : ι → V) :
    ∑ E ∈ 𝓔, ‖∑ F ∈ P.filter (fun F => r F E), x F‖ ^ 2 =
      ∑ F ∈ P, ∑ F' ∈ P, ((𝓔.filter fun E => r F E ∧ r F' E).card : ℝ) * inner ℝ (x F) (x F') := by
    classical
    calc
      ∑ E ∈ 𝓔, ‖∑ F ∈ P.filter (fun F => r F E), x F‖ ^ 2 =
          ∑ E ∈ 𝓔, ∑ F ∈ P, ∑ F' ∈ P,
            if r F E ∧ r F' E then inner ℝ (x F) (x F') else 0 := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [FunctionalInequalities.Analysis.Tensor.norm_sq_sum_eq_sum_sum_inner]
        simp only [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro F hF
        by_cases h : r F E
        · simp only [h, ↓reduceIte]
          apply Finset.sum_congr rfl
          intro F' hF'
          by_cases h' : r F' E <;> simp [h']
        · simp [h]
      _ = ∑ F ∈ P, ∑ E ∈ 𝓔, ∑ F' ∈ P,
            if r F E ∧ r F' E then inner ℝ (x F) (x F') else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ F ∈ P, ∑ F' ∈ P, ∑ E ∈ 𝓔,
            if r F E ∧ r F' E then inner ℝ (x F) (x F') else 0 := by
        apply Finset.sum_congr rfl
        intro F hF
        rw [Finset.sum_comm]
      _ = ∑ F ∈ P, ∑ F' ∈ P,
            ((𝓔.filter (fun E => r F E ∧ r F' E)).card : ℝ) *
              inner ℝ (x F) (x F') := by
        apply Finset.sum_congr rfl
        intro F hF
        apply Finset.sum_congr rfl
        intro F' hF'
        rw [← Finset.sum_filter]
        simp [nsmul_eq_mul]
