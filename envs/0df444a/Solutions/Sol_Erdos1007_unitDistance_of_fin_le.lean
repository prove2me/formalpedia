-- Prove2me | solution 1 for Erdos1007.unitDistance_of_fin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:25.952395+00:00
-- url     : https://prove2.me/submissions/5da5f691-9c9f-41ec-ba3a-bc56cfbd37ed

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Erdos1007_Geometry_FinLe
section
namespace Erdos1007
noncomputable section
private lemma appendZero_castLE {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : appendZero h x (Fin.castLE h i) = x i := by
  simp only [appendZero]
  exact (Fin.castLE_injective h).extend_apply (fun i => x i) (fun _ => (0 : ℝ)) i
private lemma appendZero_eq_zero {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n))
    {j : Fin m} (hj : j ∉ Set.range (Fin.castLE h)) : appendZero h x j = 0 := by
  simp only [appendZero]
  exact Function.extend_apply' (fun i => x i) (fun _ => (0 : ℝ)) j hj
private lemma dist_appendZero {n m : ℕ} (h : n ≤ m) (x y : EuclideanSpace ℝ (Fin n)) :
    dist (appendZero h x) (appendZero h y) = dist x y := by
  have hsum :
      (∑ j : Fin m, dist (appendZero h x j) (appendZero h y j) ^ 2) =
        ∑ i : Fin n, dist (x i) (y i) ^ 2 := by
    refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
        (fun i => dist (x i) (y i) ^ 2)
        (fun j => dist (appendZero h x j) (appendZero h y j) ^ 2) ?_ ?_).symm
    · intro j hj
      rw [appendZero_eq_zero h x hj, appendZero_eq_zero h y hj, dist_self,
        zero_pow (by decide : (2 : ℕ) ≠ 0)]
    · intro i
      rw [appendZero_castLE, appendZero_castLE]
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, hsum]
private lemma appendZero_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (appendZero h) := by
  intro x y hxy
  ext i
  simpa [appendZero_castLE] using
    congr_arg (fun z : EuclideanSpace ℝ (Fin m) => z (Fin.castLE h i)) hxy
@[expose] public section
end
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
noncomputable section
public section
namespace Erdos1007
theorem _root_.solution {V : Type*} {G : SimpleGraph V} {n m : ℕ} (h : n ≤ m) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : V → EuclideanSpace ℝ (Fin m), Function.Injective g ∧
        ∀ u v, G.Adj u v → dist (g u) (g v) = 1 := by
  rintro ⟨f, hfInj, hfDist⟩
  refine ⟨appendZero h ∘ f, (appendZero_injective h).comp hfInj, ?_⟩
  intro u v huv
  rw [Function.comp_apply, Function.comp_apply, dist_appendZero h, hfDist u v huv]
end Erdos1007
