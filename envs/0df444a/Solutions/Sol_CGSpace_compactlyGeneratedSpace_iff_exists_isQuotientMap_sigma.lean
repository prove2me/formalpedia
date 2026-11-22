-- Prove2me | solution 1 for CGSpace.compactlyGeneratedSpace_iff_exists_isQuotientMap_sigma
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:54:27.318709+00:00
-- url     : https://prove2.me/submissions/90a920ee-f2d7-40db-a648-dbb430f64063

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

theorem solution
    (X : Type u) [TopologicalSpace X] :
    CompactlyGeneratedSpace X ↔
      ∃ (I : Type u) (K : I → CompHaus.{u}) (q : (Σ i, K i) → X), IsQuotientMap q := by
  constructor
  · intro hX
    -- every non-open subset is detected by one test map from a compact Hausdorff space
    have key : ∀ s : {s : Set X // ¬ IsOpen s},
        ∃ (S : CompHaus.{u}) (f : C(S, X)), ¬ IsOpen (f ⁻¹' s.1) := by
      intro s
      by_contra h
      simp only [not_exists, not_not] at h
      exact s.2 (UCompactlyGeneratedSpace.isOpen h)
    choose S f hf using key
    -- index set: the non-open subsets of `X`, together with the points of `X`
    let K : ({s : Set X // ¬ IsOpen s} ⊕ X) → CompHaus.{u} := fun i =>
      match i with
      | Sum.inl s => S s
      | Sum.inr _ => CompHaus.of PUnit.{u + 1}
    let g : ∀ i, C(K i, X) := fun i =>
      match i with
      | Sum.inl s => f s
      | Sum.inr x => ContinuousMap.const _ x
    refine ⟨{s : Set X // ¬ IsOpen s} ⊕ X, K, fun p => g p.1 p.2, ?_⟩
    have hcont : Continuous (fun p : (Σ i, K i) => g p.1 p.2) :=
      continuous_sigma fun i => (g i).continuous
    refine (isQuotientMap_iff _).2
      ⟨isCoinducing_iff.2 fun s => ⟨fun hs => ?_, fun hs => hs.preimage hcont⟩, ?_⟩
    · -- a subset with open preimage is open: otherwise its own test map contradicts this
      by_contra hns
      exact hf ⟨s, hns⟩ (isOpen_sigma_iff.1 hs (Sum.inl ⟨s, hns⟩))
    · -- surjectivity comes from the one-point summands
      intro x
      exact ⟨⟨Sum.inr x, PUnit.unit⟩, rfl⟩
  · rintro ⟨I, K, q, hq⟩
    refine compactlyGeneratedSpace_of_isOpen fun s hs => ?_
    rw [← hq.isOpen_preimage]
    exact isOpen_sigma_iff.2 fun i =>
      hs (K i) (fun k => q ⟨i, k⟩) (hq.continuous.comp continuous_sigmaMk)
