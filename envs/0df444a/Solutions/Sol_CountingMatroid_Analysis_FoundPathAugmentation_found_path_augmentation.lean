-- Prove2me | solution 1 for CountingMatroid.Analysis.FoundPathAugmentation.found_path_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:42:41.944239+00:00
-- url     : https://prove2.me/submissions/8e51e5e7-e5fe-4d59-870d-70d2fafa3a1f

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
import Theorems.Thm_CountingMatroid_Analysis_FindPathCertificate_findPath_certificate
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearch_tabulate_val
import Theorems.Thm_CountingMatroid_Analysis_ShortestExchangeAugmentation_shortest_exchange_augmentation

namespace Arlib
end Arlib
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

/-! Proof-side certificates use the search's reverse list orientation. Minimality
is over all source-to-sink walks, not just paths discovered by the implementation. -/
namespace CountingMatroid.Analysis.ExchangePathCertificate
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch







/-- INTERNAL: Forget operation charges when toggling a list of vertices. -/
theorem toggle_fold_value {n : ℕ} (p : List (Fin n)) (I : Finset (Fin n)) :
    (Arlib.Computation.Charged.foldl toggle p I).val =
      p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I := by
  classical
  induction p generalizing I with
  | nil => rfl
  | cons i p ih =>
    rw [Arlib.Computation.Charged.val_foldl_cons]
    by_cases hi : i ∈ I <;> simpa [hi, toggle, CountingMatroid.Model.Operations.containsElement,
      CountingMatroid.Model.Operations.insertElement] using
      ih (if i ∈ I then I.erase i else insert i I)
end CountingMatroid.Analysis.ExchangePathCertificate

end
set_option autoImplicit false

/-!
The successful branch of the concrete exchange search. Correctness requires
both the algorithmic fact that the selected reverse path is shortest and the
matroid fact that toggling a shortest exchange path augments independence.
The explicit ShortestCertificate separates these obligations. The parent now
composes the two child statements; both children remain open proof obligations.
The checked value bridge removes operation charges and the certified length
bound removes the cap. Arbitrary directed paths do not satisfy the conclusion.
-/

namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FoundPathAugmentation

open CountingMatroid.Model CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: Toggling the shortest path actually returned by the capped
search preserves both matroids' independence and adds one element.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) (p : List (Fin n))
    (hp : (findPath (buildGraph o₁ o₂ I).val).val = some p) :
    let next := (Arlib.Computation.Charged.foldl toggle (p.take n) I).val
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      next.card = I.card + 1 := by
  cases n with
  | zero =>
    simp [findPath] at hp
  | succ n =>
    cases n with
    | zero =>
      classical
      let graph := (buildGraph o₁ o₂ I).val
      have hfind : (findPath graph).val =
          if (graph.terminals 0).1 && (graph.terminals 0).2 then some [0] else none := by
        cases hs : (graph.terminals 0).1 <;> cases ht : (graph.terminals 0).2 <;>
          simp [findPath, initialPaths, tabulate_val, List.finRange_succ,
            relaxPaths, relaxVertex, predecessorStep, CountingMatroid.Model.Operations.isSome,
            sinkStep, hs, ht]
      change (findPath graph).val = some p at hp
      rw [hfind] at hp
      split at hp
      · rename_i hflags
        obtain ⟨hs, ht⟩ := Bool.and_eq_true_iff.mp hflags
        have hp' : p = [0] := (Option.some.inj hp).symm
        subst p
        have hterminal : graph.terminals 0 =
            (decide ((0 : Fin 1) ∉ I ∧ M₁.Indep (insert 0 (I : Set (Fin 1)))),
             decide ((0 : Fin 1) ∉ I ∧ M₂.Indep (insert 0 (I : Set (Fin 1))))) := by
          simp only [graph, buildGraph_val]
          exact testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂ I 0
        rw [hterminal] at hs ht
        have hfirst : (0 : Fin 1) ∉ I ∧ M₁.Indep (insert 0 (I : Set (Fin 1))) := by
          simpa only [decide_eq_true_eq] using hs
        have hsecond : (0 : Fin 1) ∉ I ∧ M₂.Indep (insert 0 (I : Set (Fin 1))) := by
          simpa only [decide_eq_true_eq] using ht
        simpa [toggle, CountingMatroid.Model.Operations.containsElement,
          CountingMatroid.Model.Operations.insertElement, hfirst.1] using
          And.intro hfirst.2 (And.intro hsecond.2 (Finset.card_insert_of_notMem hfirst.1))
      · contradiction
    | succ n =>
      classical
      have hc := CountingMatroid.Analysis.FindPathCertificate.findPath_certificate
        (buildGraph o₁ o₂ I).val p hp
      have haug := CountingMatroid.Analysis.ShortestExchangeAugmentation.shortest_exchange_augmentation
        M₁ M₂ o₁ o₂ hfull h₁ h₂ I hI₁ hI₂ p hc
      dsimp only
      rw [List.take_of_length_le hc.length_le,
        CountingMatroid.Analysis.ExchangePathCertificate.toggle_fold_value]
      exact haug
