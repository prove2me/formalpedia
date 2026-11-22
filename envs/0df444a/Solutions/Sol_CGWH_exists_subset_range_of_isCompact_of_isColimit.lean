-- Prove2me | solution 1 for CGWH.exists_subset_range_of_isCompact_of_isColimit
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:50:25.657802+00:00
-- url     : https://prove2.me/submissions/cb9e00da-fd05-460b-8548-9ca1b283d6df

import Mathlib

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u


theorem solution
    {F : ℕ ⥤ TopCat.{u}} {c : Limits.Cocone F} (hc : Limits.IsColimit c)
    (hT1 : ∀ n : ℕ, T1Space (F.obj n))
    (hfin : ∀ (n : ℕ) (x : c.pt), ((c.ι.app n) ⁻¹' {x}).Finite)
    {K : Set c.pt} (hK : IsCompact K) : ∃ n : ℕ, K ⊆ Set.range (c.ι.app n) := by
  by_contra hcon
  push Not at hcon
  have hex : ∀ n, ∃ x, x ∈ K ∧ x ∉ Set.range (c.ι.app n) := fun n => Set.not_subset.mp (hcon n)
  choose x hxK hxn using hex
  have hmono : ∀ m n, m ≤ n → Set.range (c.ι.app m) ⊆ Set.range (c.ι.app n) := by
    intro m n hmn
    rintro _ ⟨y, rfl⟩
    refine ⟨F.map (homOfLE hmn) y, ?_⟩
    have := c.w (homOfLE hmn)
    rw [← this]; rfl
  have hclosed : ∀ E : Set c.pt, E ⊆ Set.range x → IsClosed E := by
    intro E hE
    rw [TopCat.isClosed_iff_of_isColimit c hc]
    intro m
    have hfinE : ((c.ι.app m) ⁻¹' E).Finite := by
      have hsub : (c.ι.app m) ⁻¹' E ⊆ ⋃ n ∈ Finset.range m, (c.ι.app m) ⁻¹' {x n} := by
        intro y hy
        obtain ⟨n, hn⟩ := hE hy
        have hnm : n < m := by
          by_contra hge
          push Not at hge
          exact hxn n (hmono m n hge ⟨y, hn.symm⟩)
        simp only [Set.mem_iUnion, Finset.mem_range]
        exact ⟨n, hnm, hn.symm⟩
      exact (Set.Finite.biUnion (Finset.finite_toSet _) (fun n _ => hfin m (x n))).subset hsub
    have := hT1 m
    exact hfinE.isClosed
  have hinf : (Set.range x).Infinite := by
    intro hf
    have hsurj : ∀ p : c.pt, ∃ n, p ∈ Set.range (c.ι.app n) := by
      intro p
      obtain ⟨j, y, hy⟩ := Limits.Concrete.isColimit_exists_rep F hc p
      exact ⟨j, y, hy⟩
    choose N hN using hsurj
    obtain ⟨M, hM⟩ := (hf.image N).bddAbove
    exact hxn M (hmono _ _ (hM (Set.mem_image_of_mem N (Set.mem_range_self M))) (hN (x M)))
  have hcomp : IsCompact (Set.range x) :=
    hK.of_isClosed_subset (hclosed _ subset_rfl) (Set.range_subset_iff.mpr hxK)
  have hdisc : DiscreteTopology (Set.range x) := by
    rw [discreteTopology_iff_forall_isClosed]
    intro s
    have h1 := hclosed (Subtype.val '' s) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    have h2 := h1.preimage (continuous_subtype_val (p := fun y => y ∈ Set.range x))
    rwa [Set.preimage_image_eq _ Subtype.val_injective] at h2
  have : CompactSpace (Set.range x) := isCompact_iff_compactSpace.mp hcomp
  exact hinf (Set.finite_coe_iff.mp finite_of_compact_of_discrete)

