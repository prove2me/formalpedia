-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.global_candidate_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T05:58:01.639159+00:00
-- url     : https://prove2.me/submissions/c0f85391-0cb6-49ef-87ef-999ec0177c9c

import Definitions.Def_ChenCapacityTerminals_Exact_RootedHeadline

set_option autoImplicit false

open ChenCapacityTerminals.Exact

private lemma cut_reverse (G : Network) (X : Finset ℕ) (hG : G.Valid)
    (hX : X ⊆ G.vertices) :
    cut (reverseNetwork G) X = cut G (G.vertices \ X) := by
  classical
  simp only [cut, weight, reverseNetwork, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  have hv := hG e he
  by_cases ht : e.tail ∈ X <;> by_cases hh : e.head ∈ X <;> simp_all

private lemma global_complement_comparison (G : Network) (r : ℕ)
    (hG : G.Valid) (Y Z : Finset ℕ)
    (hY : OptimalRoot (reverseNetwork G) r Y) (hZ : GlobalSide G Z)
    (hrZ : r ∈ Z) : cut G (G.vertices \ Y) ≤ cut G Z := by
  have hYsub : Y ⊆ G.vertices := hY.1.1
  have hvs : RootSide (reverseNetwork G) r (G.vertices \ Z) := by
    refine ⟨by simp [reverseNetwork], ?_, ?_⟩
    · obtain ⟨z, hz, hzZ⟩ : ∃ z, z ∈ G.vertices ∧ z ∉ Z := by
        by_contra hn
        push_neg at hn
        exact hZ.2.2 (Finset.Subset.antisymm hZ.1 hn)
      exact ⟨z, by simp [hz, hzZ]⟩
    · simp [hrZ]
  have hopt := hY.2 (G.vertices \ Z) hvs
  have hZZ : G.vertices \ (G.vertices \ Z) = Z := by
    ext z
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hzV, hn⟩
      by_contra hzZ
      exact hn ⟨hzV, hzZ⟩
    · intro hzZ
      exact ⟨hZ.1 hzZ, by simp [hzZ]⟩
  rw [cut_reverse G Y hG hYsub] at hopt
  rw [← hZZ]
  rw [← cut_reverse G (G.vertices \ Z) hG Finset.sdiff_subset]
  exact hopt

theorem solution (G : Network) (r : ℕ) (hr : r ∈ G.vertices)
    (hG : G.Valid) (X Y : Finset ℕ) (hX : OptimalRoot G r X)
    (hY : OptimalRoot (reverseNetwork G) r Y) :
    OptimalGlobal G (if cut G X ≤ cut G (G.vertices \ Y) then X else G.vertices \ Y) := by
  classical
  have hXsub : X ⊆ G.vertices := hX.1.1
  have hYsub : Y ⊆ G.vertices := hY.1.1
  have hXne : X.Nonempty := hX.1.2.1
  have hYne : Y.Nonempty := hY.1.2.1
  have hrX : r ∉ X := hX.1.2.2
  have hrY : r ∉ Y := hY.1.2.2
  have hcompYsub : G.vertices \ Y ⊆ G.vertices := Finset.sdiff_subset
  have hcompYne : (G.vertices \ Y).Nonempty := ⟨r, by simp [hr, hrY]⟩
  have hXglobal : GlobalSide G X := by
    refine ⟨hXsub, hXne, ?_⟩
    intro heq
    have : r ∈ X := heq ▸ hr
    exact hrX this
  have hcompYglobal : GlobalSide G (G.vertices \ Y) := by
    refine ⟨hcompYsub, hcompYne, ?_⟩
    intro heq
    obtain ⟨y, hy⟩ := hYne
    have hmem : y ∈ G.vertices \ Y := by rw [heq]; exact hYsub hy
    exact (Finset.mem_sdiff.mp hmem).2 hy
  by_cases hle : cut G X ≤ cut G (G.vertices \ Y)
  · rw [if_pos hle]
    refine ⟨hXglobal, ?_⟩
    intro Z hZ
    by_cases hrZ : r ∈ Z
    · exact hle.trans (global_complement_comparison G r hG Y Z hY hZ hrZ)
    · exact hX.2 Z ⟨hZ.1, hZ.2.1, hrZ⟩
  · rw [if_neg hle]
    refine ⟨hcompYglobal, ?_⟩
    intro Z hZ
    by_cases hrZ : r ∈ Z
    · exact global_complement_comparison G r hG Y Z hY hZ hrZ
    · have hopt : cut G X ≤ cut G Z := hX.2 Z ⟨hZ.1, hZ.2.1, hrZ⟩
      exact (le_of_not_ge hle).trans hopt
