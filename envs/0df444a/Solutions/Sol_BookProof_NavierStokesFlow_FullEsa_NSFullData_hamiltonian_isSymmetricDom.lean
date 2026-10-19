-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.NSFullData.hamiltonian_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:29:42.409817+00:00
-- url     : https://prove2.me/submissions/7740ae98-2cf4-4a2f-8dac-e254abd4bee3

import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.hamiltonian_isSymmetricDom
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)
theorem h43_sd_add {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
    {A B : D →ₗ[ℂ] D} (hA : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom A)
    (hB : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom B) :
    BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom (A + B) := by
  intro x y
  simp only [LinearMap.add_apply, Submodule.coe_add, inner_add_left, inner_add_right, hA x y, hB x y]

theorem h43_sd_sub {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
    {A B : D →ₗ[ℂ] D} (hA : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom A)
    (hB : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom B) :
    BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom (A - B) := by
  intro x y
  simp only [LinearMap.sub_apply, Submodule.coe_sub, inner_sub_left, inner_sub_right, hA x y, hB x y]

theorem h43_sd_sum {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
    {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)}
    (hA : ∀ i ∈ s, BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom (A i)) :
    BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x y; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact h43_sd_add (hA a (Finset.mem_insert_self a s))
      (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

theorem h43_sd_comp_comm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
    {A B : D →ₗ[ℂ] D} (hA : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom A)
    (hB : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom B) (hc : A.comp B = B.comp A) :
    BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom (A.comp B) := by
  intro x y
  have : A (B y) = B (A y) := by simpa using congrArg (fun T => T y) hc
  simp only [LinearMap.comp_apply]
  rw [hA, hB, this]

theorem h43_sd_anticomm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
    {A B : D →ₗ[ℂ] D} (hA : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom A)
    (hB : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom B) :
    BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom (A.comp B + B.comp A) := by
  intro x y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add, inner_add_left,
    inner_add_right]
  rw [hA, hB, hB, hA, add_comm]

theorem h43_advection_symm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (d : BookProof.NavierStokesFlow.FullEsa.NSFullData F) (i : Fin 3) :
    BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom (d.advection i) := by
  unfold BookProof.NavierStokesFlow.FullEsa.NSFullData.advection
  refine h43_sd_sub (h43_sd_sum _ fun j _ => h43_sd_comp_comm (d.u_symm _) (d.u_symm _) (d.u_comm _ _))
    (BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.real_smul (d.u_symm _) _)

theorem solution : IsSymmetricDom d.hamiltonian := by
  unfold BookProof.NavierStokesFlow.FullEsa.NSFullData.hamiltonian
  exact h43_sd_sum _ fun i _ => h43_sd_anticomm (d.mom_symm i) (h43_advection_symm d i)

