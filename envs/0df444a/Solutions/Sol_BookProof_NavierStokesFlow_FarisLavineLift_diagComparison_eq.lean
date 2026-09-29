-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_eq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:18:58.724152+00:00
-- url     : https://prove2.me/submissions/05becfea-dfa3-4f40-a0a6-1a09233fef8c

import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
set_option autoImplicit false
set_option maxHeartbeats 4000000
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
namespace BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.DiagonalEsa
theorem diagOp_add (a b : ℕ → ℝ) : diagOp a + diagOp b = diagOp (fun n => a n + b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.add_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, diagOp_coe,
    diagFun, Complex.ofReal_add]
  ring
theorem diagOp_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ) :
    (∑ i ∈ s, diagOp (a i)) = diagOp (fun n => ∑ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
      funext n
      simp [diagFun]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, ih, diagOp_add]
      congr 1
      funext n
      rw [Finset.sum_insert hx]
end BookProof.NavierStokesFlow.FullEsa
namespace BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.DiagonalEsa
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
namespace ComparisonData
variable {d : ℕ} (c : ComparisonData F d)
theorem comparison_isSymmetricDom : IsSymmetricDom c.comparison := by
  have hid : IsSymmetricDom (LinearMap.id : c.D →ₗ[ℂ] c.D) := by
    intro x y
    simp
  refine IsSymmetricDom.add (IsSymmetricDom.add ?_ ?_) hid
  · exact IsSymmetricDom.sum Finset.univ fun i _ =>
      (c.mom_symm i).comp_of_commute (c.mom_symm i) rfl
  · exact IsSymmetricDom.sum Finset.univ fun i _ =>
      (c.drift_symm i).comp_of_commute (c.drift_symm i) rfl
end ComparisonData
theorem diagOp_one :
    (LinearMap.id : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ) = diagOp (fun _ => 1) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp [diagOp, diagFun]
theorem diagComparison_eq (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    (diagComparisonData d p q).comparison
      = diagOp (fun k => (∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1) := by
  change ((∑ i : Fin d, (diagOp (p i)).comp (diagOp (p i)))
      + (∑ i : Fin d, (diagOp (q i)).comp (diagOp (q i)))
      + (LinearMap.id : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ)) = _
  simp_rw [FullEsa.diagOp_comp]
  rw [FullEsa.diagOp_sum, FullEsa.diagOp_sum, diagOp_one, FullEsa.diagOp_add, FullEsa.diagOp_add]
  simp only [pow_two]

end BookProof.NavierStokesFlow.FarisLavineLift

open _root_.BookProof.NavierStokesFlow.DiagonalEsa
open _root_.BookProof.NavierStokesFlow
open _root_.BookProof.NavierStokesFlow.FarisLavineLift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {d : ℕ} (c : ComparisonData F d)

theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    (diagComparisonData d p q).comparison
      = diagOp (fun k => (∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1) := by
  exact BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_eq d p q

#print axioms solution
