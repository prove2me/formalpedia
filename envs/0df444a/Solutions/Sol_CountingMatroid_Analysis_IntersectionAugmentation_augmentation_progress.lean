-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionAugmentation.augmentation_progress
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:43:40.638282+00:00
-- url     : https://prove2.me/submissions/626ea1b9-9b71-43c7-9aa4-30aad7ef66e7

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
import Theorems.Thm_CountingMatroid_Analysis_ExchangeClosedBasis_exchange_closed_basis
import Theorems.Thm_CountingMatroid_Analysis_FoundPathAugmentation_found_path_augmentation
import Theorems.Thm_CountingMatroid_Analysis_IntersectionAugmentation_separator_card_le
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearch_tabulate_val
import Theorems.Thm_CountingMatroid_Analysis_NoPathSeparator_no_path_separator

namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
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
set_option autoImplicit false

/-!
The augmentation-progress proof combines exact exchange-query predicates,
a graph separator when search fails, and shortest-path exchange preservation
when search succeeds. The matroid basis certificates on both sides of the
separator are proved here using `ExchangeClosedBasis`. Graph-search saturation
is proved in `NoPathSeparator`; successful-path preservation remains an
explicit obligation in `FoundPathAugmentation`. This is an internal refinement
of the cited pretest, not an additional oracle or an assumed contract.
-/

namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.IntersectionAugmentation

open CountingMatroid.Model CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: A concrete shortest-path augmentation either increases common
independence by one element or leaves a maximum common independent set fixed.
This separates the mathematical exchange argument from the independent
unconditional resource accounting for exactly the same implementation.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) :
    let next := (augmentOnce o₁ o₂ I).val
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      (next.card = I.card + 1 ∨
        (next = I ∧ ∀ J : Finset (Fin n),
          M₁.Indep (J : Set (Fin n)) → M₂.Indep (J : Set (Fin n)) → J.card ≤ I.card)) := by
  classical
  dsimp only
  unfold augmentOnce
  simp only [Arlib.Computation.Charged.val_bind]
  cases hp : (findPath (buildGraph o₁ o₂ I).val).val with
  | none =>
    simp only [Arlib.Computation.Charged.val_pure]
    refine ⟨hI₁, hI₂, Or.inr ⟨trivial, ?_⟩⟩
    intro J hJ₁ hJ₂
    let graph := (buildGraph o₁ o₂ I).val
    obtain ⟨R, hsource, hedge, hsink⟩ :=
      NoPathSeparator.no_path_separator graph hp
    have hsources (e : Fin n) : (graph.terminals e).1 = true ↔
        e ∉ I ∧ M₁.Indep (insert e (I : Set (Fin n))) := by
      simp only [graph, buildGraph_val, testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂,
        decide_eq_true_eq]
    have hsinks (e : Fin n) : (graph.terminals e).2 = true ↔
        e ∉ I ∧ M₂.Indep (insert e (I : Set (Fin n))) := by
      simp only [graph, buildGraph_val, testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂,
        decide_eq_true_eq]
    have harcs (u v : Fin n) : graph.edges u v = true ↔
        (u ∈ I ∧ v ∉ I ∧ M₁.Indep
          (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)))) ∨
        (u ∉ I ∧ v ∈ I ∧ M₂.Indep
          (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n)))) := by
      simp only [graph, buildGraph_val, testEdge_val M₁ M₂ o₁ o₂ h₁ h₂,
        decide_eq_true_eq]
    refine separator_card_le M₁ M₂ I R ?_ ?_ J hJ₁ hJ₂
    · have hb := ExchangeClosedBasis.exchange_closed_basis M₁
        (I : Set (Fin n)) (Set.univ \ (R : Set (Fin n))) hI₁
        (by rw [hfull.1]; exact Set.subset_univ _) ?_ ?_
      · simpa only [Finset.coe_sdiff, Finset.coe_univ,
          ← Set.inter_sdiff_assoc, Set.inter_univ] using hb
      · intro e he heI hind
        exact he.2 (hsource e ((hsources e).mpr ⟨heI, hind⟩))
      · intro e he heI u hu hind
        refine ⟨Set.mem_univ u, ?_⟩
        intro huR
        apply he.2
        apply hedge u e huR
        apply (harcs u e).mpr
        exact Or.inl ⟨hu, heI, by simpa only [Finset.coe_erase] using hind⟩
    · have hb := ExchangeClosedBasis.exchange_closed_basis M₂
        (I : Set (Fin n)) (R : Set (Fin n)) hI₂
        (by rw [hfull.2]; exact Set.subset_univ _) ?_ ?_
      · simpa only [Finset.coe_inter] using hb
      · intro e he heI hind
        have ht := (hsinks e).mpr ⟨heI, hind⟩
        rw [hsink e he] at ht
        contradiction
      · intro e he heI u hu hind
        apply hedge e u he
        apply (harcs e u).mpr
        exact Or.inr ⟨heI, hu, by simpa only [Finset.coe_erase] using hind⟩
  | some p =>
    obtain ⟨hnext₁, hnext₂, hcard⟩ :=
      FoundPathAugmentation.found_path_augmentation M₁ M₂ o₁ o₂ hfull h₁ h₂ I hI₁ hI₂ p hp
    exact ⟨hnext₁, hnext₂, Or.inl hcard⟩
