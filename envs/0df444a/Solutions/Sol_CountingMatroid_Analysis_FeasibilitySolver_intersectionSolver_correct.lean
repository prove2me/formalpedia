-- Prove2me | solution 1 for CountingMatroid.Analysis.FeasibilitySolver.intersectionSolver_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:44:42.566638+00:00
-- url     : https://prove2.me/submissions/4f21752d-e7e0-4aef-bc5a-3b945cf010e0

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
import Definitions.Def_CountingMatroid_Analysis_FeasibilitySolver
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
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
import Theorems.Thm_CountingMatroid_Analysis_IntersectionAugmentation_augmentation_progress

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
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
set_option autoImplicit false

/-!
The common-base predicate is connected to the paper's feasibility pretest.
Ranks zero and one are implemented and verified using the charged interface;
the rank-one implementation is the first augmentation from the empty set.
An explicit capped exchange-graph implementation handles arbitrary rank.
Its uniform cost certificate is proved. The parent now reduces correctness to
the augmentation-progress obligation in a separate child file, which remains
open. The parent proof has no open tactic goals but depends on that obligation.
-/

namespace CountingMatroid.Analysis.FeasibilitySolver
end CountingMatroid.Analysis.FeasibilitySolver
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines
open CountingMatroid.Model
open scoped Classical

/-- INTERNAL: Iterating the concrete augmentation at most `r` times reaches
size `r` exactly when a size-`r` common independent set exists. The loop invariant
compares its cardinality with every common independent competitor.
TEXLINE: main.tex:283-289 -/
theorem solution (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) :
    (IntersectionSearch.intersectionSolver.run n r o₁ o₂).val = decide
      (∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n))) := by
  classical
  have hloop (l : List ℕ) (I : Finset (Fin n))
      (hI₁ : M₁.Indep (I : Set (Fin n))) (hI₂ : M₂.Indep (I : Set (Fin n))) :
      let result := (Arlib.Computation.Charged.foldl
        (fun I _ => IntersectionSearch.augmentOnce o₁ o₂ I) l I).val
      M₁.Indep (result : Set (Fin n)) ∧ M₂.Indep (result : Set (Fin n)) ∧
        I.card ≤ result.card ∧ result.card ≤ I.card + l.length ∧
        ∀ J : Finset (Fin n), M₁.Indep (J : Set (Fin n)) →
          M₂.Indep (J : Set (Fin n)) → min (I.card + l.length) J.card ≤ result.card := by
    induction l generalizing I with
    | nil =>
      simp only [Arlib.Computation.Charged.val_foldl_nil, List.length_nil, Nat.add_zero]
      exact ⟨hI₁, hI₂, le_rfl, le_rfl, fun J _ _ => min_le_left _ _⟩
    | cons j l ih =>
      simp only [Arlib.Computation.Charged.val_foldl_cons, List.length_cons]
      let next := (IntersectionSearch.augmentOnce o₁ o₂ I).val
      have hp := IntersectionAugmentation.augmentation_progress M₁ M₂ o₁ o₂
        hfull h₁ h₂ I hI₁ hI₂
      obtain ⟨hout₁, hout₂, hlower, hupper, hcompare⟩ := ih next hp.1 hp.2.1
      have hstep : I.card ≤ next.card ∧ next.card ≤ I.card + 1 := by
        rcases hp.2.2 with hincrease | ⟨hfixed, _⟩
        · change next.card = I.card + 1 at hincrease
          omega
        · change next = I at hfixed
          rw [hfixed]
          omega
      refine ⟨hout₁, hout₂, hstep.1.trans hlower, ?_, ?_⟩
      · calc
          _ ≤ next.card + l.length := hupper
          _ ≤ I.card + (l.length + 1) := by omega
      intro J hJ₁ hJ₂
      rcases hp.2.2 with hincrease | ⟨hfixed, hmax⟩
      · have hcomp := hcompare J hJ₁ hJ₂
        change next.card = I.card + 1 at hincrease
        have heq : I.card + (l.length + 1) = next.card + l.length := by omega
        simpa only [heq] using hcomp
      · change next = I at hfixed
        have hJ := hmax J hJ₁ hJ₂
        have hJnext : J.card ≤ next.card := by
          rw [hfixed]
          exact hJ
        exact (min_le_right _ _).trans (hJnext.trans hlower)
  let result := (Arlib.Computation.Charged.foldl
    (fun I _ => IntersectionSearch.augmentOnce o₁ o₂ I) (List.range r)
      (∅ : Finset (Fin n))).val
  have hresult := hloop (List.range r) ∅ (by simp) (by simp)
  change M₁.Indep (result : Set (Fin n)) ∧ M₂.Indep (result : Set (Fin n)) ∧
    0 ≤ result.card ∧ result.card ≤ 0 + (List.range r).length ∧
    (∀ J : Finset (Fin n), M₁.Indep (J : Set (Fin n)) →
      M₂.Indep (J : Set (Fin n)) → min (0 + (List.range r).length) J.card ≤ result.card)
    at hresult
  simp only [List.length_range, Nat.zero_add] at hresult
  have hiff : result.card = r ↔ ∃ I : Finset (Fin n), I.card = r ∧
      M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
    constructor
    · intro hcard
      exact ⟨result, hcard, hresult.1, hresult.2.1⟩
    · rintro ⟨J, hcard, hJ₁, hJ₂⟩
      have hlower := hresult.2.2.2.2 J hJ₁ hJ₂
      rw [hcard, min_self] at hlower
      exact Nat.le_antisymm hresult.2.2.2.1 hlower
  change (result.card == r) = _
  have hbool : (result.card == r) = true ↔
      ∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
    simpa only [beq_iff_eq] using hiff
  cases hvalue : (result.card == r) <;> simp_all
