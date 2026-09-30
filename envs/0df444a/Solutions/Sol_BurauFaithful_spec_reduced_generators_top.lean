-- Prove2me | solution 1 for BurauFaithful.spec_reduced_generators_top
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T03:02:01.039621+00:00
-- url     : https://prove2.me/submissions/ff5f143a-074a-4984-8002-87a78673b786

/-
`BurauFaithful.spec_reduced_generators_top`: the two matrices that are the images of `σ₀` and `σ₁`
under the specialization at `t = -1` of the 2-dimensional reduced Burau representation generate
the homogeneous modular group `M₂ = SL(2,ℤ)`.

`Mathlib` provides `SpecialLinearGroup.SL2Z_generators : closure {S, T} = ⊤` for
`S = !![0,-1;1,0]`, `T = !![1,1;0,1]`. With `A = !![1,-1;0,1]` and `B = !![2,-1;1,0]` one has
`T = A⁻¹` and `S = A² · B`, so `S, T` lie in the closure of `{A, B}`, whence that closure is `⊤`.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup

theorem solution :
    Subgroup.closure
      ({⟨!![1, -1; 0, 1], by decide⟩, ⟨!![2, -1; 1, 0], by decide⟩} :
        Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) = ⊤ := by
  set A : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, -1; 0, 1], by decide⟩ with hA
  set B : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![2, -1; 1, 0], by decide⟩ with hB
  have h1 : A ∈ Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :=
    Subgroup.subset_closure (by simp)
  have h2 : B ∈ Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :=
    Subgroup.subset_closure (by simp)
  have hS : ModularGroup.S ∈ Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    have h : ModularGroup.S = A ^ 2 * B := by
      ext i j
      fin_cases i <;> fin_cases j <;> decide
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 2) h2
  have hT : ModularGroup.T ∈ Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    have h : ModularGroup.T = A⁻¹ := by
      ext i j
      fin_cases i <;> fin_cases j <;> decide
    rw [h]
    exact Subgroup.inv_mem _ h1
  have hST : ({ModularGroup.S, ModularGroup.T} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ⊆
      Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hS
    · exact hT
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ≤
      Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    rw [← SpecialLinearGroup.SL2Z_generators]
    rw [Subgroup.closure_le]
    exact hST
  exact top_le_iff.mp htop
