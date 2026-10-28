-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.apply_eq_of_image_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:42.094469+00:00
-- url     : https://prove2.me/submissions/60605312-15dd-4d09-9a0c-e2cd01cc3d9c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

noncomputable section
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- If `v` is invariant under the permutations supported in `A` and in `B` (disjoint), then
`ρ σ v` for `σ` fixing everything outside `A ∪ B` depends only on the image `σ(A)`. -/
theorem solution (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B : Finset Ω} (v : V)
    (hvA : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside B, ρ σ v = v)
    {σ τ : Equiv.Perm Ω} (hσ : σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (A ∪ B)) (hτ : τ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (A ∪ B))
    (h : A.image σ = A.image τ) : ρ σ v = ρ τ v := by
    let π : Equiv.Perm Ω := τ⁻¹ * σ
    have hπ : π ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (A ∪ B) := by
      simp only [FunctionalInequalities.Analysis.Tensor.fixingOutside, mem_filter, mem_univ, true_and] at hσ hτ ⊢
      intro x hx
      have hs : σ x = x := hσ x hx
      have ht : τ x = x := hτ x hx
      have hti : τ⁻¹ x = x := by
        apply τ.injective
        calc
          τ (τ⁻¹ x) = x := τ.apply_symm_apply x
          _ = τ x := ht.symm
      change τ⁻¹ (σ x) = x
      rw [hs, hti]

    have hπfix : ∀ x, x ∉ A ∪ B → π x = x := by
      simpa [FunctionalInequalities.Analysis.Tensor.fixingOutside] using hπ

    have hA : ∀ x, x ∈ A ↔ π x ∈ A := by
      intro x
      constructor
      · intro hx
        have htx : σ x ∈ A.image τ := by
          rw [← h]
          exact mem_image_of_mem σ hx
        rcases mem_image.mp htx with ⟨y, hy, hxy⟩
        have hπxy : π x = y := by
          apply τ.injective
          calc
            τ (π x) = σ x := by simp [π]
            _ = τ y := hxy.symm
        rw [hπxy]
        exact hy
      · intro hx
        have hst : σ x ∈ A.image τ := by
          have hxy : σ x = τ (π x) := by simp [π]
          rw [hxy]
          exact mem_image_of_mem τ hx
        have hss : σ x ∈ A.image σ := by
          rw [h]
          exact hst
        rcases mem_image.mp hss with ⟨y, hy, hxy⟩
        have hyx : y = x := σ.injective hxy
        simpa [hyx] using hy

    have hA' : ∀ x, π x ∈ A ↔ x ∈ A := fun x => (hA x).symm

    let α : Equiv.Perm Ω := Equiv.Perm.ofSubtype (π.subtypePerm hA')
    have hαA : ∀ x, x ∈ A → α x = π x := by
      intro x hx
      change (Equiv.Perm.ofSubtype (π.subtypePerm hA')) x = π x
      exact Equiv.Perm.ofSubtype_apply_of_mem (π.subtypePerm hA') hx

    have hαnot : ∀ x, x ∉ A → α x = x := by
      intro x hx
      change (Equiv.Perm.ofSubtype (π.subtypePerm hA')) x = x
      exact Equiv.Perm.ofSubtype_apply_of_not_mem (π.subtypePerm hA') hx

    have hα : α ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside A := by
      simp only [FunctionalInequalities.Analysis.Tensor.fixingOutside, mem_filter, mem_univ, true_and]
      intro x hx
      exact hαnot x hx

    let β : Equiv.Perm Ω := α⁻¹ * π
    have hβ : β ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside B := by
      simp only [FunctionalInequalities.Analysis.Tensor.fixingOutside, mem_filter, mem_univ, true_and]
      intro x hxB
      by_cases hxA : x ∈ A
      · have hπxA : π x ∈ A := (hA x).mp hxA
        have hi : α⁻¹ (π x) = x := by
          apply α.injective
          calc
            α (α⁻¹ (π x)) = π x := α.apply_symm_apply (π x)
            _ = α x := (hαA x hxA).symm
        change α⁻¹ (π x) = x
        exact hi
      · have hxU : x ∉ A ∪ B := by
          simp [hxA, hxB]
        have hπx : π x = x := hπfix x hxU
        have hαx : α x = x := hαnot x hxA
        have hαix : α⁻¹ x = x := by
          apply α.injective
          calc
            α (α⁻¹ x) = x := α.apply_symm_apply x
            _ = α x := hαx.symm
        change α⁻¹ (π x) = x
        rw [hπx]
        exact hαix

    have hpab : α * β = π := by
      simp [β]

    have hpv : ρ π v = v := by
      calc
        ρ π v = ρ (α * β) v := by rw [hpab]
        _ = ρ α (ρ β v) := by simp
        _ = ρ α v := by rw [hvB β hβ]
        _ = v := hvA α hα

    have hτσ : τ * π = σ := by
      simp [π]

    calc
      ρ σ v = ρ (τ * π) v := by rw [hτσ]
      _ = ρ τ (ρ π v) := by simp
      _ = ρ τ v := by rw [hpv]
