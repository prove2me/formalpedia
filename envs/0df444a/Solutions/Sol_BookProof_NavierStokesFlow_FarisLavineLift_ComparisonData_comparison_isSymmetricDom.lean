-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T22:34:59.357578+00:00
-- url     : https://prove2.me/submissions/1f53b78c-edbe-4e25-a2cc-d93db466a8dd

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFarisLavineLift.lean -/
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterNavierStokesFullEsa
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### Closure properties of `IsSymmetricDom`

These three lemmas are stated in `BookProof.ChapterNavierStokesFullEsa` but are not
part of the published `Definitions.Def_ChapterNavierStokesFullEsa` module, so they are
re-proved here, verbatim from the source chapter. -/

namespace BookProof.NavierStokesFlow.FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem IsSymmetricDom.add {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) :
    IsSymmetricDom (A + B) := by
  intro x y
  simp only [LinearMap.add_apply, Submodule.coe_add, inner_add_left, inner_add_right, hA x y,
    hB x y]

theorem IsSymmetricDom.sum {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)}
    (hA : ∀ i ∈ s, IsSymmetricDom (A i)) : IsSymmetricDom (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (IsSymmetricDom.zero (D := D))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hA a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

theorem IsSymmetricDom.comp_of_commute {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) (hcomm : A.comp B = B.comp A) : IsSymmetricDom (A.comp B) := by
  intro x y
  have h1 : (inner ℂ ((A (B x) : F)) (y : F) : ℂ) = inner ℂ ((B x : F)) ((A y : F)) := hA _ _
  have h2 : (inner ℂ ((B x : F)) ((A y : F)) : ℂ) = inner ℂ (x : F) ((B (A y) : F)) := hB _ _
  have h3 : B (A y) = A (B y) := by
    have := congrArg (fun T : D →ₗ[ℂ] D => T y) hcomm
    simpa using this.symm
  simpa [h3] using h1.trans h2

end BookProof.NavierStokesFlow.FullEsa

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_isSymmetricDom
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {d : ℕ} (c : ComparisonData F d)

/-- The comparison operator `n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I` is symmetric on its domain:
each `πᵢ²` and each `Vᵢ²` is the square of a symmetric domain-preserving operator,
hence symmetric, and the identity is symmetric. -/
theorem solution : IsSymmetricDom c.comparison := by
  have hid : IsSymmetricDom (LinearMap.id : c.D →ₗ[ℂ] c.D) := by
    intro x y
    simp
  refine IsSymmetricDom.add (IsSymmetricDom.add ?_ ?_) hid
  · exact IsSymmetricDom.sum Finset.univ fun i _ =>
      (c.mom_symm i).comp_of_commute (c.mom_symm i) rfl
  · exact IsSymmetricDom.sum Finset.univ fun i _ =>
      (c.drift_symm i).comp_of_commute (c.drift_symm i) rfl
