-- Prove2me | solution 1 for CountingMatroid.Analysis.ShortestExchangeAugmentation.shortest_exchange_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:41:42.580506+00:00
-- url     : https://prove2.me/submissions/b0c55e61-ab15-4af6-8040-a7b89c02fa0f

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
import Definitions.Def_CountingMatroid_Analysis_ExchangeWalkReversal
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_ExchangeWalkCardinality_augmenting_walk_cardinality
import Theorems.Thm_CountingMatroid_Analysis_ExchangeWalkReversal_source_walk_iff_chain
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearch_tabulate_val
import Theorems.Thm_CountingMatroid_Analysis_ShortestSourceWalkIndependence_shortest_source_walk_independence
import Theorems.Thm_CountingMatroid_Analysis_ShortestSourceWalkIndependence_toggle_fold_symmDiff

namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
section


set_option autoImplicit false

/-!
Concrete bounded exchange-graph search for the feasibility pretest. Oracle
answers are obtained only through `oracleQuery`; the graph, path tables, and
set updates are charged. Breadth-first layers use a frozen previous table,
so the first path recorded at a vertex has minimum length. Path lists are
capped at `n` entries, and the outer solver performs exactly `r` augmentations.
The elementary query specifications are proved here. The common-independence
and maximum-cardinality theorem and the uniform cost certificate belong to
separate proof files.
-/

namespace CountingMatroid.Analysis.IntersectionSearch

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical











/-- INTERNAL: Encoded set queries decode to exactly the represented subset. -/
theorem decode_membership {n : ℕ} (I : Finset (Fin n)) :
    decode (fun i => decide (i ∈ I)) = (I : Set (Fin n)) := by
  ext i
  simp [decode]

/-- INTERNAL: Exact terminal flags for the current exchange graph. -/
theorem testTerminal_val {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (I : Finset (Fin n)) (i : Fin n) :
    (testTerminal o₁ o₂ I i).val =
      (decide (i ∉ I ∧ M₁.Indep (insert i (I : Set (Fin n)))),
       decide (i ∉ I ∧ M₂.Indep (insert i (I : Set (Fin n))))) := by
  classical
  change ((!decide (i ∈ I) && o₁ (fun j => decide (j ∈ insert i I))),
    (!decide (i ∈ I) && o₂ (fun j => decide (j ∈ insert i I)))) = _
  rw [h₁, h₂, decode_membership, Finset.coe_insert]
  by_cases hi : i ∈ I <;> simp [hi]

/-- INTERNAL: Exact directed edge predicate computed by the two charged
exchange queries. No single-matroid augmentation assumption is used. -/
theorem testEdge_val {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (I : Finset (Fin n)) (u v : Fin n) :
    (testEdge o₁ o₂ I u v).val = decide
      ((u ∈ I ∧ v ∉ I ∧ M₁.Indep (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)))) ∨
       (u ∉ I ∧ v ∈ I ∧ M₂.Indep (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n))))) := by
  classical
  change ((decide (u ∈ I) && !decide (v ∈ I) &&
    o₁ (fun j => decide (j ∈ insert v (I.erase u)))) ||
    (!decide (u ∈ I) && decide (v ∈ I) &&
    o₂ (fun j => decide (j ∈ insert u (I.erase v))))) = _
  rw [h₁, h₂, decode_membership, decode_membership, Finset.coe_insert, Finset.coe_insert]
  by_cases hu : u ∈ I <;> by_cases hv : v ∈ I <;> simp [hu, hv]



/-- INTERNAL: Building the graph materializes the terminal and edge tests;
this lets the path proof use their exact mathematical specifications. -/
theorem buildGraph_val {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) :
    (buildGraph o₁ o₂ I).val =
      ⟨fun i => (testTerminal o₁ o₂ I i).val,
       fun u v => (testEdge o₁ o₂ I u v).val⟩ := by
  simp [buildGraph, tabulate_val]





















end CountingMatroid.Analysis.IntersectionSearch

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r15 · construction · built capped charged exchange-graph, synchronous breadth-first search, and rank-many augmentations; proved exact query and table specifications. A three-element partition-oracle probe verified an exchange requiring removal of the current element.
-/

end

section


set_option autoImplicit false

/-! Reversing an exchange graph interchanges its sources and sinks. Reverse
list paths then satisfy the same augmentation and shortestness predicates. -/
namespace CountingMatroid.Analysis.ExchangeWalkReversal
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate





/-- INTERNAL: Augmenting walks are adjacent-edge chains whose last vertex
is a source and whose first vertex is a sink. -/
theorem augmenting_walk_iff_chain {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) :
    AugmentingWalk g p ↔
      p.IsChain (fun v u => g.edges u v = true) ∧
        (∃ v, p.getLast? = some v ∧ (g.terminals v).1 = true) ∧
        (∃ v, p.head? = some v ∧ (g.terminals v).2 = true) := by
  rw [AugmentingWalk, source_walk_iff_chain]
  constructor
  · rintro ⟨⟨hchain, hlast⟩, v, tail, heq, hs⟩
    exact ⟨hchain, hlast, v, List.head?_eq_some_iff.mpr ⟨tail, heq⟩, hs⟩
  · rintro ⟨hchain, hlast, v, hhead, hs⟩
    obtain ⟨tail, heq⟩ := List.head?_eq_some_iff.mp hhead
    exact ⟨⟨hchain, hlast⟩, v, tail, heq, hs⟩

/-- INTERNAL: Reverse an augmenting walk to exchange the roles of the two
matroids in the single-matroid independence argument. -/
theorem augmenting_walk_reverse {n : ℕ} {g : ExchangeGraph n} {p : List (Fin n)}
    (hw : AugmentingWalk g p) : AugmentingWalk (reverse_exchange_graph g) p.reverse := by
  obtain ⟨hchain, hlast, hhead⟩ := (augmenting_walk_iff_chain g p).mp hw
  apply (augmenting_walk_iff_chain (reverse_exchange_graph g) p.reverse).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact List.isChain_reverse.mpr hchain
  · simpa only [List.getLast?_reverse, reverse_exchange_graph] using hhead
  · simpa only [List.head?_reverse, reverse_exchange_graph] using hlast

/-- INTERNAL: Global shortestness and simplicity survive graph and list
reversal, so the second matroid uses the same certified induction. -/
theorem shortest_certificate_reverse {n : ℕ} {g : ExchangeGraph n}
    {p : List (Fin n)} (hc : ShortestCertificate g p) :
    ShortestCertificate (reverse_exchange_graph g) p.reverse := by
  refine ⟨augmenting_walk_reverse hc.augmenting,
    List.nodup_reverse.mpr hc.simple, ?_, ?_⟩
  · simpa only [List.length_reverse] using hc.length_le
  · intro q hq
    have hrev := augmenting_walk_reverse hq
    change AugmentingWalk g q.reverse at hrev
    simpa only [List.length_reverse] using hc.minimal q.reverse hrev

end CountingMatroid.Analysis.ExchangeWalkReversal

end
set_option autoImplicit false

/-! Mathematical half of augmentation: this file does not mention findPath or
its BFS tables. Global shortestness rules out the shortcuts needed in the
simultaneous-exchange argument. Fundamental-circuit induction establishes
independence for the first matroid, graph reversal establishes it for the second,
and alternating membership establishes the cardinality increment. -/
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ShortestExchangeAugmentation
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate
open CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid.Analysis.ExchangeWalkReversal
open scoped symmDiff

/-- INTERNAL: A shortest exchange-graph path augments both independent sets.
This isolates the matroid argument from the executable search and its charges.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) (p : List (Fin n))
    (hc : ShortestCertificate (buildGraph o₁ o₂ I).val p) :
    let next := p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      next.card = I.card + 1 := by
  classical
  have ht (v : Fin n) :
      ((buildGraph o₁ o₂ I).val.terminals v).1 = true ↔
        v ∉ I ∧ M₁.Indep (insert v (I : Set (Fin n))) := by
    simp only [buildGraph_val, testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂,
      decide_eq_true_eq]
  have he (u v : Fin n) : (buildGraph o₁ o₂ I).val.edges u v = true ↔
      (u ∈ I ∧ v ∉ I ∧ M₁.Indep (insert v (↑(I.erase u) : Set (Fin n)))) ∨
      (u ∉ I ∧ v ∈ I ∧ M₂.Indep (insert u (↑(I.erase v) : Set (Fin n)))) := by
    simp only [buildGraph_val, testEdge_val M₁ M₂ o₁ o₂ h₁ h₂,
      decide_eq_true_eq]
  have halt (u v : Fin n) (huv : (buildGraph o₁ o₂ I).val.edges u v = true) :
      (u ∈ I ∧ v ∉ I) ∨ (u ∉ I ∧ v ∈ I) := by
    rcases (he u v).mp huv with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  have hexch (u v : Fin n) (hu : u ∈ I) (hv : v ∉ I) :
      (buildGraph o₁ o₂ I).val.edges u v = true ↔
        M₁.Indep (insert v (↑(I.erase u) : Set (Fin n))) := by
    rw [he]
    simp only [hu, hv, not_true_eq_false, not_false_eq_true, true_and,
      false_and, or_false]
  have hmin : ∀ v tail, p = v :: tail → ∀ q,
      SourceWalk (buildGraph o₁ o₂ I).val (v :: q) →
      p.length ≤ (v :: q).length := by
    intro v tail hp q hq
    obtain ⟨w, rest, heq, hsink⟩ := hc.augmenting.2
    have hvw := (List.cons.inj (hp.symm.trans heq)).1
    subst w
    exact hc.minimal (v :: q) ⟨hq, v, q, rfl, hsink⟩
  dsimp only
  rw [toggle_fold_symmDiff I p hc.simple]
  refine ⟨?_, ?_, ?_⟩
  · exact (shortest_source_walk_independence M₁ (buildGraph o₁ o₂ I).val I
      hfull.1 hI₁ ht halt hexch p hc.augmenting.1 hc.simple hmin).1
  · have hc' := shortest_certificate_reverse hc
    have ht' (v : Fin n) :
        ((reverse_exchange_graph (buildGraph o₁ o₂ I).val).terminals v).1 = true ↔
          v ∉ I ∧ M₂.Indep (insert v (I : Set (Fin n))) := by
      simp only [reverse_exchange_graph, buildGraph_val,
        testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂, decide_eq_true_eq]
    have halt' (u v : Fin n)
        (huv : (reverse_exchange_graph (buildGraph o₁ o₂ I).val).edges u v = true) :
        (u ∈ I ∧ v ∉ I) ∨ (u ∉ I ∧ v ∈ I) := by
      rcases halt v u huv with ⟨hv, hu⟩ | ⟨hv, hu⟩
      · exact Or.inr ⟨hu, hv⟩
      · exact Or.inl ⟨hu, hv⟩
    have hexch' (u v : Fin n) (hu : u ∈ I) (hv : v ∉ I) :
        (reverse_exchange_graph (buildGraph o₁ o₂ I).val).edges u v = true ↔
          M₂.Indep (insert v (↑(I.erase u) : Set (Fin n))) := by
      change (buildGraph o₁ o₂ I).val.edges v u = true ↔ _
      rw [he]
      simp only [hu, hv, not_true_eq_false, not_false_eq_true, true_and,
        false_and, false_or]
    have hmin' : ∀ v tail, p.reverse = v :: tail → ∀ q,
        SourceWalk (reverse_exchange_graph (buildGraph o₁ o₂ I).val) (v :: q) →
        p.reverse.length ≤ (v :: q).length := by
      intro v tail hp q hq
      obtain ⟨w, rest, heq, hsink⟩ := hc'.augmenting.2
      have hvw := (List.cons.inj (hp.symm.trans heq)).1
      subst w
      exact hc'.minimal (v :: q) ⟨hq, v, q, rfl, hsink⟩
    simpa only [List.toFinset_reverse] using
      (shortest_source_walk_independence M₂
        (reverse_exchange_graph (buildGraph o₁ o₂ I).val) I hfull.2 hI₂
        ht' halt' hexch' p.reverse hc'.augmenting.1 hc'.simple hmin').1
  · simpa only [toggle_fold_symmDiff I p hc.simple] using
      CountingMatroid.Analysis.ExchangeWalkCardinality.augmenting_walk_cardinality
        M₁ M₂ o₁ o₂ h₁ h₂ I p hc.augmenting hc.simple
