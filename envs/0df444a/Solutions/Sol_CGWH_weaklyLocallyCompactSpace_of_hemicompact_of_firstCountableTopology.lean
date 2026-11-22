-- Prove2me | solution 1 for CGWH.weaklyLocallyCompactSpace_of_hemicompact_of_firstCountableTopology
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:52:45.984477+00:00
-- url     : https://prove2.me/submissions/8931422c-243b-464e-a015-84924cbdd1c6

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

theorem solution
    (X : Type*) [TopologicalSpace X] [FirstCountableTopology X]
    (h : ∃ S : Set (Set X), S.Countable ∧ (∀ K ∈ S, IsCompact K) ∧
      ∀ C : Set X, IsCompact C → ∃ K ∈ S, C ⊆ K) :
    WeaklyLocallyCompactSpace X := by
  obtain ⟨S, hSc, hSk, hScof⟩ := h
  have hne : S.Nonempty := by
    obtain ⟨K, hK, -⟩ := hScof ∅ isCompact_empty
    exact ⟨K, hK⟩
  obtain ⟨e, he⟩ := hSc.exists_eq_range hne
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU⟩ := (𝓝 x).exists_antitone_basis
  by_contra hcon
  have hex : ∀ n, ∃ y, y ∈ U n ∧ y ∉ e n := by
    intro n
    by_contra hn
    push_neg at hn
    exact hcon ⟨e n, hSk _ (he ▸ Set.mem_range_self n),
      Filter.mem_of_superset (hU.mem n) hn⟩
  choose y hyU hye using hex
  have hy : Filter.Tendsto y Filter.atTop (𝓝 x) := hU.tendsto hyU
  have hcomp : IsCompact (insert x (Set.range y)) := hy.isCompact_insert_range
  obtain ⟨K, hK, hsub⟩ := hScof _ hcomp
  rw [he] at hK
  obtain ⟨N, rfl⟩ := hK
  exact hye N (hsub (Set.mem_insert_of_mem _ (Set.mem_range_self N)))
