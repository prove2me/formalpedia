-- Prove2me | solution 1 for CrossingConsequences.unitDistanceGraph_counting_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:07:10.078398+00:00
-- url     : https://prove2.me/submissions/4e53e0de-4d4d-4812-af85-ae0b3b2343da

import Mathlib

set_option autoImplicit false

open Classical

namespace CrossingConsequences
namespace P2MAlias

/-- The canonical unit-distance graph on a finite point set `P` in the Euclidean
plane: two distinct points of `P` are adjacent iff they are at distance exactly 1. -/
noncomputable def unitDistanceGraph (P : Finset (EuclideanSpace ℝ (Fin 2))) : SimpleGraph P :=
  SimpleGraph.fromRel (fun u v : P => u ≠ v ∧ dist (u : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 2)) = 1)

end P2MAlias
end CrossingConsequences

open Classical CrossingConsequences.P2MAlias in
theorem e0236751_key (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card
      ≤ 2 * (unitDistanceGraph P).edgeFinset.card := by
  calc (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card
      ≤ (Finset.univ.image (fun d : (unitDistanceGraph P).Dart =>
          (((d.fst : P) : EuclideanSpace ℝ (Fin 2)), ((d.snd : P) : EuclideanSpace ℝ (Fin 2))))).card := by
        apply Finset.card_le_card
        intro pq hpq
        simp only [Finset.mem_filter, Finset.mem_offDiag] at hpq
        obtain ⟨⟨h1, h2, hne⟩, hd⟩ := hpq
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        have hadj : (unitDistanceGraph P).Adj ⟨pq.1, h1⟩ ⟨pq.2, h2⟩ := by
          have hne' : (⟨pq.1, h1⟩ : P) ≠ ⟨pq.2, h2⟩ := fun h => hne (congrArg Subtype.val h)
          simp only [unitDistanceGraph, SimpleGraph.fromRel_adj]
          exact ⟨hne', Or.inl ⟨hne', hd⟩⟩
        exact ⟨⟨(⟨pq.1, h1⟩, ⟨pq.2, h2⟩), hadj⟩, rfl⟩
    _ ≤ (Finset.univ : Finset (unitDistanceGraph P).Dart).card := Finset.card_image_le
    _ = 2 * (unitDistanceGraph P).edgeFinset.card := by
        rw [Finset.card_univ]
        convert SimpleGraph.dart_card_eq_twice_card_edges (G := unitDistanceGraph P)

open Classical CrossingConsequences.P2MAlias in
theorem solution (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ((((P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2 : ℕ)) : ℝ) - (P.card : ℝ)
      ≤ (((unitDistanceGraph P).edgeFinset.card : ℕ) : ℝ) := by
  have h : (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2
      ≤ (unitDistanceGraph P).edgeFinset.card :=
    Nat.div_le_of_le_mul (e0236751_key P)
  have h' : (((P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2 : ℕ) : ℝ)
      ≤ (((unitDistanceGraph P).edgeFinset.card : ℕ) : ℝ) := by exact_mod_cast h
  have hP : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  linarith
