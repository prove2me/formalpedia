-- Prove2me | solution 1 for BaconThesis.DFS.lemma_5_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:15:49.004023+00:00
-- url     : https://prove2.me/submissions/87b85d25-01a7-49f7-8850-03eaedce27e4

import Mathlib
import Definitions.Def_BaconThesis_DFS_osrOp
import Definitions.Def_BaconThesis_DFS_osrAlgebra

open scoped Kronecker Pointwise

open BaconThesis.DFS in
theorem solution {s e ι : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype ι]
    (Sα : ι → Matrix s s ℂ) (Bα : ι → Matrix e e ℂ) (t : ℝ) (φ ψ : e → ℂ) :
    osrOp (∑ α, Sα α ⊗ₖ Bα α) t φ ψ ∈ osrAlgebra Sα := by
  classical
  set H := ∑ α, Sα α ⊗ₖ Bα α with hH
  set G : Set (Matrix (s × e) (s × e) ℂ) :=
    {X | ∃ A ∈ osrAlgebra Sα, ∃ C : Matrix e e ℂ, X = A ⊗ₖ C} with hG
  set Wsub : Submodule ℂ (Matrix (s × e) (s × e) ℂ) := Submodule.span ℂ G with hWsub
  have hGG : G * G ⊆ G := by
    intro X hX
    obtain ⟨Y, hY, Z, hZ, rfl⟩ := Set.mem_mul.mp hX
    obtain ⟨A, hA, C, rfl⟩ := hY
    obtain ⟨A', hA', C', rfl⟩ := hZ
    exact ⟨A * A', Subalgebra.mul_mem _ hA hA', C * C', (Matrix.mul_kronecker_mul _ _ _ _).symm⟩
  have hone : (1 : Matrix (s × e) (s × e) ℂ) ∈ Wsub :=
    Submodule.subset_span ⟨1, Subalgebra.one_mem _, 1, (Matrix.one_kronecker_one).symm⟩
  have hmul : ∀ x y : Matrix (s × e) (s × e) ℂ, x ∈ Wsub → y ∈ Wsub → x * y ∈ Wsub := by
    intro x y hx hy
    have h := Submodule.mul_mem_mul hx hy
    rw [hWsub, Submodule.span_mul_span] at h
    exact Submodule.span_mono hGG h
  set W := Wsub.toSubalgebra hone hmul with hW
  have hclosed : IsClosed (W : Set (Matrix (s × e) (s × e) ℂ)) :=
    Wsub.closed_of_finiteDimensional
  have hHW : H ∈ W := by
    show H ∈ Wsub
    rw [hH]
    apply Submodule.sum_mem
    intro α _
    exact Submodule.subset_span ⟨Sα α, Algebra.subset_adjoin ⟨α, rfl⟩, Bα α, rfl⟩
  have hexp : evolOp H t ∈ W := by
    unfold evolOp
    exact NormedSpace.exp_mem (R := ℂ) hclosed (Subalgebra.smul_mem W hHW _)
  -- the reduction map
  set Λ : Matrix (s × e) (s × e) ℂ → Matrix s s ℂ := fun X =>
    Matrix.of fun a b => ∑ k, ∑ l, star (φ k) * X (a, k) (b, l) * ψ l with hΛ
  have hosr : osrOp H t φ ψ = Λ (evolOp H t) := rfl
  rw [hosr]
  have hexp' : evolOp H t ∈ Wsub := hexp
  suffices hsuff : ∀ E ∈ Wsub, Λ E ∈ osrAlgebra Sα from hsuff _ hexp'
  intro E hE
  induction hE using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨A, hA, C, rfl⟩ := hX
    have : Λ (A ⊗ₖ C) = (∑ k, ∑ l, star (φ k) * C k l * ψ l) • A := by
      ext a b
      simp only [hΛ, Matrix.of_apply, Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      ring
    rw [this]
    exact Subalgebra.smul_mem _ hA _
  | zero =>
    have : Λ 0 = 0 := by ext a b; simp [hΛ]
    rw [this]; exact Subalgebra.zero_mem _
  | add X Y _ _ hX hY =>
    have : Λ (X + Y) = Λ X + Λ Y := by
      ext a b
      simp only [hΛ, Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    rw [this]; exact Subalgebra.add_mem _ hX hY
  | smul c X _ hX =>
    have : Λ (c • X) = c • Λ X := by
      ext a b
      simp only [hΛ, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      ring
    rw [this]; exact Subalgebra.smul_mem _ hX _
