-- Prove2me | solution 1 for DLevelNestedLogit.Assortment.root_local_iff_optimal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:54:59.780062+00:00
-- url     : https://prove2.me/submissions/1c8596a0-a456-4b85-82f5-b9e92649145e

import Mathlib
import Definitions.Def_DLevelNestedLogit_Assortment_Tree
import Definitions.Def_DLevelNestedLogit_Assortment_Choice

open DLevelNestedLogit.Assortment DLevelNestedLogit.Assortment.ProductTree in
theorem solution (n : ℕ) (T : ProductTree n) (η : T.Node → ℝ)
    (v r : Fin (n + 1) → ℝ) (hη : T.StandingEta η) (hv : ∀ i, 0 < v i)
    (Sstar S : Finset (Fin (n + 1))) :
    T.tparent η v r Sstar T.root = 0 ∧
    (∀ S', T.localObj η v r T.root (T.tparent η v r Sstar T.root) S' = T.R η v r S' T.root) ∧
    (T.IsLocalOptimal η v r T.root (T.tparent η v r Sstar T.root) S ↔
      T.IsOptimalAssortment η v r S) := by
  have hroot_nl : ¬ T.IsLeaf T.root := fun ⟨i, hi⟩ => T.leaf_ne_root i hi
  have hV : ∀ S', T.V η v S' T.root = 1 := by
    intro S'
    rw [ProductTree.V, dif_neg hroot_nl, hη.1, Real.rpow_zero]
  have htp : T.tparent η v r Sstar T.root = 0 := by
    unfold ProductTree.tparent; rw [if_pos rfl]
  have hloc : ∀ S', T.localObj η v r T.root 0 S' = T.R η v r S' T.root := by
    intro S'; unfold ProductTree.localObj; rw [hV]; ring
  have hNleaf : ∀ i, i ∈ T.N (T.leaf i) := by
    intro i
    rw [ProductTree.N, dif_pos ⟨i, rfl⟩]
    have : T.leafIndex (T.leaf i) ⟨i, rfl⟩ = i :=
      T.leaf_injective (Classical.choose_spec (⟨i, rfl⟩ : T.IsLeaf (T.leaf i)))
    rw [this]
    exact Finset.mem_singleton_self i
  have hup : ∀ k, k ≠ T.root → ∀ i, i ∈ T.N k → i ∈ T.N (T.parent k) := by
    intro k hk i hi
    have hpl : ¬ T.IsLeaf (T.parent k) := fun ⟨i', hi'⟩ => T.leaf_no_child i' k hk hi'.symm
    rw [ProductTree.N, dif_neg hpl]
    have hkc : k ∈ T.children (T.parent k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨⟨k, hkc⟩, Finset.mem_attach _ _, hi⟩
  have hall : ∀ m, ∀ j, T.depth j ≤ m → ∀ i, i ∈ T.N j → i ∈ T.N T.root := by
    intro m
    induction m with
    | zero =>
      intro j hj i hi
      by_cases hjr : j = T.root
      · rw [← hjr]; exact hi
      · have := T.depth_parent j hjr; omega
    | succ m ih =>
      intro j hj i hi
      by_cases hjr : j = T.root
      · rw [← hjr]; exact hi
      · exact ih (T.parent j) (by have := T.depth_parent j hjr; omega) i (hup j hjr i hi)
  have hNroot : T.N T.root = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun i => hall _ (T.leaf i) le_rfl i (hNleaf i)
  refine ⟨htp, fun S' => by rw [htp, hloc], ?_⟩
  unfold ProductTree.IsLocalOptimal ProductTree.IsOptimalAssortment
  rw [htp, hNroot]
  simp only [hloc, Finset.subset_univ, true_and, forall_const]
