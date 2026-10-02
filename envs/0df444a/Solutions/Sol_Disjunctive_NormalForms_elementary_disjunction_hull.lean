-- Prove2me | solution 1 for Disjunctive.NormalForms.elementary_disjunction_hull
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:32:53.256737+00:00
-- url     : https://prove2.me/submissions/fb82898e-a8a4-4a41-bb7c-43cb60dea654

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

set_option autoImplicit false

namespace Disjunctive.NormalForms

open Set in
lemma a444942c_isClosed {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : IsClosed (HalfspaceGE d d0) := by
  unfold HalfspaceGE
  apply isClosed_le continuous_const
  change Continuous fun x : Fin n → ℝ => ∑ i, d i * x i
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)

open Set in
lemma a444942c_convex {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Convex ℝ (HalfspaceGE d d0) := by
  intro x hx y hy a b ha hb hab
  simp only [HalfspaceGE, mem_ofPred_eq] at *
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have e : d0 = a * d0 + b * d0 := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

open Set in
/-- Two incomparable halfspaces have convex hull of their union equal to everything. -/
lemma a444942c_two {n : ℕ} (a b : Fin n → ℝ) (α β : ℝ) (x y : Fin n → ℝ)
    (hx : α ≤ a ⬝ᵥ x) (hx' : b ⬝ᵥ x < β) (hy : β ≤ b ⬝ᵥ y) (hy' : a ⬝ᵥ y < α)
    (S : Set (Fin n → ℝ)) (hA : HalfspaceGE a α ⊆ S) (hB : HalfspaceGE b β ⊆ S)
    (z : Fin n → ℝ) : z ∈ convexHull ℝ S := by
  set u := x - y with hu
  have hau : 0 < a ⬝ᵥ u := by rw [hu, dotProduct_sub]; linarith
  have hbu : b ⬝ᵥ u < 0 := by rw [hu, dotProduct_sub]; linarith
  set t : ℝ := max ((α - a ⬝ᵥ z) / (a ⬝ᵥ u)) ((β - b ⬝ᵥ z) / (-(b ⬝ᵥ u))) with ht
  have ht1 : (α - a ⬝ᵥ z) / (a ⬝ᵥ u) ≤ t := le_max_left _ _
  have ht2 : (β - b ⬝ᵥ z) / (-(b ⬝ᵥ u)) ≤ t := le_max_right _ _
  have h1 : z + t • u ∈ S := by
    apply hA
    simp only [HalfspaceGE, mem_ofPred_eq]
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [div_le_iff₀ hau] at ht1
    linarith
  have h2 : z - t • u ∈ S := by
    apply hB
    simp only [HalfspaceGE, mem_ofPred_eq]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hnb : 0 < -(b ⬝ᵥ u) := by linarith
    rw [div_le_iff₀ hnb] at ht2
    nlinarith
  have hseg : segment ℝ (z + t • u) (z - t • u) ⊆ convexHull ℝ S :=
    segment_subset_convexHull h1 h2
  apply hseg
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  module

end Disjunctive.NormalForms

open Set Disjunctive.NormalForms in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] [Nonempty Q]
    (d : Q → Fin n → ℝ)
    (d0 : Q → ℝ) :
    ((¬ ∃ k, (⋃ i : Q, HalfspaceGE (d i) (d0 i)) = HalfspaceGE (d k) (d0 k)) →
        closure (convexHull ℝ (⋃ i : Q, HalfspaceGE (d i) (d0 i))) = Set.univ) ∧
      (∀ k, (⋃ i : Q, HalfspaceGE (d i) (d0 i)) = HalfspaceGE (d k) (d0 k) →
        closure (convexHull ℝ (⋃ i : Q, HalfspaceGE (d i) (d0 i))) = HalfspaceGE (d k) (d0 k)) := by
  refine ⟨?_, ?_⟩
  · intro hnot
    obtain ⟨k, -, hk⟩ := Set.Finite.exists_maximalFor
      (fun i => HalfspaceGE (d i) (d0 i)) Set.univ Set.finite_univ Set.univ_nonempty
    have hsub : ∀ i, HalfspaceGE (d i) (d0 i) ⊆ ⋃ i : Q, HalfspaceGE (d i) (d0 i) :=
      fun i => subset_iUnion (fun i => HalfspaceGE (d i) (d0 i)) i
    have hne : (⋃ i : Q, HalfspaceGE (d i) (d0 i)) ≠ HalfspaceGE (d k) (d0 k) :=
      fun h => hnot ⟨k, h⟩
    have : ∃ j, ¬ HalfspaceGE (d j) (d0 j) ⊆ HalfspaceGE (d k) (d0 k) := by
      by_contra hcon
      push_neg at hcon
      exact hne (Subset.antisymm (iUnion_subset hcon) (hsub k))
    obtain ⟨j, hj⟩ := this
    have hkj : ¬ HalfspaceGE (d k) (d0 k) ⊆ HalfspaceGE (d j) (d0 j) := by
      intro h
      exact hj (hk (Set.mem_univ j) h)
    obtain ⟨y, hy, hy'⟩ := not_subset.mp hj
    obtain ⟨x, hx, hx'⟩ := not_subset.mp hkj
    simp only [HalfspaceGE, mem_ofPred_eq, not_le] at hx hx' hy hy'
    rw [eq_univ_iff_forall]
    intro z
    apply subset_closure
    exact a444942c_two (d k) (d j) (d0 k) (d0 j) x y hx hx' hy hy' _ (hsub k) (hsub j) z
  · intro k hk
    rw [hk, (a444942c_convex (d k) (d0 k)).convexHull_eq,
      (a444942c_isClosed (d k) (d0 k)).closure_eq]
