-- Prove2me | solution 1 for CrossingConsequences.unitDistanceGraph_edgeFinset_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:07:20.285599+00:00
-- url     : https://prove2.me/submissions/b48cc32a-ef56-48e5-b775-907111bfae2e

import Mathlib

set_option autoImplicit false

open Classical

/-! 8e00445b CrossingConsequences.unitDistanceGraph_edgeFinset_card.
The target's preamble defines `CrossingConsequences.unitDistanceGraph` inline (no Definitions
bundle). A proof may not import its own target module, and redeclaring the same name would clash
with it, so the statement below is written against a local alias with an IDENTICAL body under a
distinct namespace; it is definitionally equal to the target's constant. -/
namespace CrossingConsequencesSol

noncomputable def unitDistanceGraph (P : Finset (EuclideanSpace ℝ (Fin 2))) : SimpleGraph P :=
  SimpleGraph.fromRel (fun u v : P => u ≠ v ∧ dist (u : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 2)) = 1)

theorem unitDistanceGraph_adj_iff (P : Finset (EuclideanSpace ℝ (Fin 2))) (u v : P) :
    (unitDistanceGraph P).Adj u v ↔
      u ≠ v ∧ dist (u : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 2)) = 1 := by
  unfold unitDistanceGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, (⟨-, h1⟩ | ⟨-, h1⟩)⟩
    · exact ⟨h, h1⟩
    · exact ⟨h, by rw [dist_comm]; exact h1⟩
  · rintro ⟨h, h1⟩
    exact ⟨h, Or.inl ⟨h, h1⟩⟩

end CrossingConsequencesSol

open CrossingConsequencesSol in
theorem solution (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (unitDistanceGraph P).edgeFinset.card * 2 =
      (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card := by
  have h := SimpleGraph.dart_card_eq_twice_card_edges (G := unitDistanceGraph P)
  rw [mul_comm, ← h, ← Finset.card_univ]
  refine Finset.card_bij
    (fun d _ => ((d.fst : EuclideanSpace ℝ (Fin 2)), (d.snd : EuclideanSpace ℝ (Fin 2))))
    ?_ ?_ ?_
  · intro d _
    have hd := (unitDistanceGraph_adj_iff P d.fst d.snd).1 d.adj
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    exact ⟨⟨d.fst.2, d.snd.2, fun e => hd.1 (Subtype.ext e)⟩, hd.2⟩
  · intro d₁ _ d₂ _ he
    simp only [Prod.mk.injEq] at he
    exact SimpleGraph.Dart.ext _ _ (Prod.ext (Subtype.ext he.1) (Subtype.ext he.2))
  · intro pq hpq
    simp only [Finset.mem_filter, Finset.mem_offDiag] at hpq
    obtain ⟨⟨h1, h2, hne⟩, hd⟩ := hpq
    exact ⟨⟨(⟨pq.1, h1⟩, ⟨pq.2, h2⟩),
      (unitDistanceGraph_adj_iff P _ _).2 ⟨fun e => hne (congrArg Subtype.val e), hd⟩⟩,
      Finset.mem_univ _, rfl⟩
