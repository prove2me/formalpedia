-- Prove2me | solution 1 for CountingMatroid.Analysis.ExchangeWalkCardinality.source_walk_card_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:07:07.567769+00:00
-- url     : https://prove2.me/submissions/a58ef5e5-f63c-4527-983e-d6281f529da4

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
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
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
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
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearch_tabulate_val

namespace Arlib
end Arlib
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
set_option autoImplicit false

/-! Cardinality of the symmetric difference with a simple alternating
source-to-sink exchange walk. This argument uses no matroid exchange theorem. -/
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ExchangeWalkCardinality
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: An exchange walk alternates outside and inside the original
independent set, starting outside. Its imbalance is determined by its head. -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (I : Finset (Fin n)) {p : List (Fin n)}
    (hw : SourceWalk (buildGraph o₁ o₂ I).val p) :
    ∀ v tail, p = v :: tail →
      (p.filter (fun i => decide (i ∉ I))).length =
        (p.filter (fun i => decide (i ∈ I))).length + (if v ∈ I then 0 else 1) := by
  classical
  induction hw with
  | source v hs =>
    intro w tail heq
    obtain ⟨hvw, hrest⟩ := List.cons.inj heq
    subst w
    subst tail
    have ht := testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂ I v
    have hv : v ∉ I := by
      have : v ∉ I ∧ M₁.Indep (insert v (I : Set (Fin n))) := by
        simpa only [buildGraph_val, ht, decide_eq_true_eq] using hs
      exact this.1
    simp [hv]
  | step u v tail hw he ih =>
    intro w rest heq
    obtain ⟨hvw, hrest⟩ := List.cons.inj heq
    subst w
    subst rest
    have h := ih u tail rfl
    have hedge := testEdge_val M₁ M₂ o₁ o₂ h₁ h₂ I u v
    have he' : (u ∈ I ∧ v ∉ I ∧ M₁.Indep
        (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)))) ∨
        (u ∉ I ∧ v ∈ I ∧ M₂.Indep
        (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n)))) := by
      simpa only [buildGraph_val, hedge, decide_eq_true_eq] using he
    rcases he' with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩
    · simp only [List.filter_cons, hu, hv, not_false_eq_true, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, Nat.add_zero] at h ⊢
      omega
    · simp only [List.filter_cons, hu, hv, not_false_eq_true, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, Nat.add_zero] at h ⊢
      omega
