-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.terminal_group
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T06:25:37.985274+00:00
-- url     : https://prove2.me/submissions/71d83665-d1ee-4af8-83f1-cee89deea081

import Theorems.Thm_ChenCapacityTerminals_Exact_enclosure_properties
import Theorems.Thm_ChenCapacityTerminals_Exact_optimal_augmented_projection
import Theorems.Thm_ChenCapacityTerminals_Exact_flowCutAnswer_optimal
import Theorems.Thm_ChenCapacityTerminals_Exact_exists_lawfulExactOracle

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution (G : Network) (r : ℕ) (J : Finset ℕ) (U : ℝ)
    (b : ℕ → ℕ) (hG : G.Valid) (hr : r ∈ G.vertices)
    (hJ : J ⊆ G.vertices \ {r}) (hne : J.Nonempty) (hU : 0 < U)
    (hb : ∀ v ∈ G.vertices \ {r}, 1 + indegree G v ≤ b v) :
    (∀ B, Enclosure G r J U B →
      (∀ t ∈ J \ B, ∀ X, PairSide G r t X → U ≤ cut G X) ∧
      (∀ t ∈ J ∩ B, ∃ X, OptimalPair G r t X ∧ X ⊆ B) ∧
      cut G B ≤ U * (J ∩ B).card ∧
      (∀ η : ℝ, 0 < η → Conditioned G r b η →
        (mass b B : ℝ) ≤ U / η * (J ∩ B).card)) ∧
    (∀ z, z ∉ G.vertices →
      (∃ X, OptimalPair (enclosureNetwork G J U z) r z X) ∧
      ∀ X, OptimalPair (enclosureNetwork G J U z) r z X →
        Enclosure G r J U (X.erase z)) ∧
    (∃ O, LawfulExactOracle O) ∧
    (∀ O, LawfulExactOracle O → ∀ z, z ∉ G.vertices →
      Enclosure G r J U ((O ⟨enclosureNetwork G J U z, r, z⟩).shore.erase z)) := by
  classical
  have hrz (z : ℕ) (hz : z ∉ G.vertices) : r ≠ z := by
    intro h
    apply hz
    rw [← h]
    exact hr
  have hvalid (z : ℕ) (hz : z ∉ G.vertices) :
      (enclosureNetwork G J U z).Valid := by
    intro e he
    simp only [enclosureNetwork, List.mem_append, List.mem_map] at he
    rcases he with he | ⟨t, ht, rfl⟩
    · exact (hG e he).imp (fun h => Finset.mem_insert_of_mem h) (fun h =>
        ⟨Finset.mem_insert_of_mem h.1, h.2⟩)
    · have htJ : t ∈ J := Finset.mem_toList.mp ht
      have htG : t ∈ G.vertices := (Finset.mem_sdiff.mp (hJ htJ)).1
      exact ⟨Finset.mem_insert_of_mem htG, Finset.mem_insert_self z G.vertices,
        le_of_lt hU⟩
  have hquery (z : ℕ) (hz : z ∉ G.vertices) :
      (⟨enclosureNetwork G J U z, r, z⟩ : ExactQuery).Valid := by
    exact ⟨hvalid z hz, Finset.mem_insert_of_mem hr,
      Finset.mem_insert_self z G.vertices, hrz z hz⟩
  have hoptimal (O : ExactQuery → ExactAnswer) (hO : LawfulExactOracle O)
      (z : ℕ) (hz : z ∉ G.vertices) :
      OptimalPair (enclosureNetwork G J U z) r z
        (O ⟨enclosureNetwork G J U z, r, z⟩).shore := by
    apply flowCutAnswer_optimal
    exact (hO ⟨enclosureNetwork G J U z, r, z⟩ (hquery z hz)).2
  refine ⟨?_, ?_, exists_lawfulExactOracle, ?_⟩
  · intro B hB
    exact enclosure_properties G r J U b hG hJ hU B hB
  · intro z hz
    refine ⟨?_, optimal_augmented_projection G r J U z hG hr hJ hz⟩
    obtain ⟨O, hO⟩ := exists_lawfulExactOracle
    exact ⟨(O ⟨enclosureNetwork G J U z, r, z⟩).shore, hoptimal O hO z hz⟩
  · intro O hO z hz
    exact optimal_augmented_projection G r J U z hG hr hJ hz _ (hoptimal O hO z hz)
