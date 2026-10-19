-- Prove2me | solution 1 for CompactnessConjecture.maximum_sharp_pruning_subgraph_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/1228d875-617c-4a76-8de3-79af89c6c2d9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_edgeFinset_card_eq_natCard
import Theorems.Thm_CompactnessConjecture_degree_eq_natCard_neighborSet
import Theorems.Thm_CompactnessConjecture_natCard_support_le_card
import Theorems.Thm_CompactnessConjecture_natCard_support_deleteIncidence_add_one_le

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (base H : SimpleGraph V) [DecidableRel H.Adj]
    (originalEdges : ℕ) (hHB : H ≤ base)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningPotential originalEdges D ≤
        sharpPruningPotential originalEdges H)
    {v : V} (hv : v ∈ H.support) :
    originalEdges ≤ 2 * Fintype.card V * H.degree v := by
  classical
  let D := H.deleteIncidenceSet v
  have hDB : D ≤ base :=
    le_trans (SimpleGraph.deleteIncidenceSet_le H v) hHB
  have hscore := hmax D hDB
  have hdrop : Nat.card D.support + 1 ≤ Nat.card H.support :=
    natCard_support_deleteIncidence_add_one_le H hv
  have hsupport : Nat.card H.support ≤ Fintype.card V :=
    natCard_support_le_card H
  have hcomplement :
      Fintype.card V - Nat.card H.support + 1 ≤
        Fintype.card V - Nat.card D.support := by
    omega
  have hweightedComplement :
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges ≤
        originalEdges * (Fintype.card V - Nat.card D.support) := by
    calc
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges =
        originalEdges * (Fintype.card V - Nat.card H.support + 1) := by
          simp [Nat.mul_add]
      _ ≤ originalEdges * (Fintype.card V - Nat.card D.support) :=
        Nat.mul_le_mul_left originalEdges hcomplement
  have hdeleted :
      Nat.card D.edgeSet =
        Nat.card H.edgeSet - Nat.card (H.neighborSet v) := by
    simpa only [D, edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.card_edgeFinset_deleteIncidenceSet H v)
  have hdegreeEdges :
      Nat.card (H.neighborSet v) ≤ Nat.card H.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.degree_le_card_edgeFinset H v)
  have hedgeAdd :
      Nat.card D.edgeSet + Nat.card (H.neighborSet v) =
        Nat.card H.edgeSet := by
    omega
  have hweightedEdges :
      2 * Fintype.card V * Nat.card H.edgeSet =
        2 * Fintype.card V * Nat.card D.edgeSet +
          2 * Fintype.card V * Nat.card (H.neighborSet v) := by
    rw [← hedgeAdd, mul_add]
  change
    2 * Fintype.card V * Nat.card D.edgeSet +
        originalEdges * (Fintype.card V - Nat.card D.support) ≤
      2 * Fintype.card V * Nat.card H.edgeSet +
        originalEdges * (Fintype.card V - Nat.card H.support)
    at hscore
  simp only [degree_eq_natCard_neighborSet]
  omega
end CompactnessConjecture
