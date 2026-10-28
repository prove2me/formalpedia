-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservationRoundDrawSites.chain_abort_draw_site
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:29:26.608317+00:00
-- url     : https://prove2.me/submissions/7df97b77-2f1a-47d7-9971-fd1a53d28573

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_ClassifiedStateSelection_classified_state_selection
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_boundedUniform_result_lt
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_classified_defect_distinct

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
section


set_option autoImplicit false

/-!
Abort attribution for a chain attempt from a non-invalid state. Successful
bounded draws return in-range indices, classified states have weight values,
and the imported selection correctness invariant excludes failed lookups.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Model CountingMatroid.Program





/-- INTERNAL: A non-invalid classifier always has an actual weight value. -/
theorem classified_weight_exists {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (hvalid : (classifyState state).val ≠ .invalid) :
    ∃ w, (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val = some w := by
  cases hk : (classifyState state).val with
  | invalid => exact False.elim (hvalid hk)
  | transversal =>
      simp only [weightOfKind, Arlib.Computation.Charged.val_bind]
      exact ⟨_, rfl⟩
  | defect i j =>
      have hne := classified_defect_distinct state i j hk
      simp only [weightOfKind, dif_pos hne, Arlib.Computation.Charged.val_bind]
      exact ⟨_, rfl⟩



end CountingMatroid.Analysis.ObservationRoundDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r28 · closed · imported selector correctness is now proved; all abort attribution dependencies are closed.
* r28 · composed · proved sampler output range, classifier off-diagonal labels, classified weight existence, and all chain abort branches using classified_state_selection. Selection correctness is the only remaining imported child obligation.
* r28 · open · unfolded the charged chain attempt and excluded the holding
  branch; the remaining branches need the boundedUniform output range and
  executable selection correctness for classifier-valid states, followed by
  exclusion of diagonal defect weight failures.
-/

end
set_option autoImplicit false

/-!
Abort attribution for a chain attempt from a non-invalid state. Successful
bounded draws return in-range indices, classified states have weight values,
and the imported selection correctness invariant excludes failed lookups.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: On a non-invalid state, a failed chain attempt is attributable
to one of its three actual capped draws, with the descriptor stopped before
that draw. No positivity or accuracy property of the weights is required.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ)
    (hvalid : (classifyState state).val ≠ .invalid)
    (habort : (chainStep r o₁ o₂ tape s.drawTrials q weights state cursor).val = none) :
    ∃ site d, chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d ∧
      (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none := by
  unfold chainStep at habort
  simp only [Arlib.Computation.Charged.val_bind,
    Model.Operations.fairBit, Model.Operations.successor,
    Arlib.Computation.Charged.val_op] at habort
  cases hhold : tape cursor with
  | true =>
      simp only [hhold, ite_true, Arlib.Computation.Charged.val_pure] at habort
      cases habort
  | false =>
      simp only [hhold, Bool.false_eq_true, ite_false] at habort
      cases hA : (boundedUniform tape s.drawTrials n (cursor + 1)).val with
      | mk choiceA stopA =>
        cases choiceA with
        | none =>
          refine ⟨⟨0, by decide⟩, (cursor + 1, n), ?_, ?_⟩
          · simp [chainDrawSite, hhold]
          · exact congrArg Prod.fst hA
        | some aIndex =>
          simp only [hA, Arlib.Computation.Charged.val_bind] at habort
          cases hB : (boundedUniform tape s.drawTrials n stopA).val with
          | mk choiceB stopB =>
            cases choiceB with
            | none =>
              refine ⟨⟨1, by decide⟩, (stopA, n), ?_, ?_⟩
              · simp [chainDrawSite, hhold, hA]
              · exact congrArg Prod.fst hB
            | some bIndex =>
              have haIndex := boundedUniform_result_lt tape s.drawTrials n
                (cursor + 1) aIndex (by rw [hA])
              have hbIndex := boundedUniform_result_lt tape s.drawTrials n
                stopA bIndex (by rw [hB])
              obtain ⟨a, ha⟩ := ClassifiedStateSelection.classified_state_selection
                state hvalid true aIndex haIndex
              obtain ⟨b, hb⟩ := ClassifiedStateSelection.classified_state_selection
                state hvalid false bIndex hbIndex
              simp only [hB, Arlib.Computation.Charged.val_bind, ha, hb,
                Model.Operations.erasePaired, Model.Operations.insertPaired,
                Arlib.Computation.Charged.val_opMany] at habort
              let candidate : PairedSet n := insert b (state.erase a)
              change (match (classifyState candidate).val with
                | .invalid => pure (some (state, stopB))
                | _ => _ : Arlib.Computation.Charged Model.Operations.Op
                  Model.Operations.Cell (Option (PairedSet n × ℕ))).val = none at habort
              cases hkind : (classifyState candidate).val
              case invalid =>
                simp only [hkind, Arlib.Computation.Charged.val_pure] at habort
                cases habort
              all_goals
                have hnewvalid : (classifyState candidate).val ≠ .invalid := by
                  rw [hkind]
                  intro h
                  cases h
                obtain ⟨oldWeight, ho⟩ := classified_weight_exists
                  r o₁ o₂ q weights state hvalid
                obtain ⟨newWeight, hn⟩ := classified_weight_exists
                  r o₁ o₂ q weights candidate hnewvalid
                have hnKind := hn
                rw [hkind] at hnKind
                have hkRaw := hkind
                dsimp only [candidate] at hkRaw hnKind
                simp only [hkind, hkRaw, Arlib.Computation.Charged.val_bind,
                  ho, hnKind] at habort
                by_cases hneed : (Model.Operations.ratLess
                    (Model.Operations.ratDiv newWeight oldWeight).val 1).val = true
                · rw [if_pos hneed] at habort
                  have hneedProp : newWeight / oldWeight < 1 := by
                    with_unfolding_all
                      exact of_decide_eq_true hneed
                  simp only [Arlib.Computation.Charged.val_bind,
                    Model.Operations.ratDiv,
                    Model.Operations.rationalDenominator,
                    Model.Operations.rationalNumerator,
                    Arlib.Computation.Charged.val_opMany] at habort
                  cases hC : (boundedUniform tape s.drawTrials
                      (newWeight / oldWeight).den stopB).val with
                  | mk choiceC stopC =>
                    cases choiceC with
                    | none =>
                      refine ⟨⟨2, by decide⟩, (stopB, (newWeight / oldWeight).den), ?_, ?_⟩
                      · simp only [chainDrawSite, hhold, Bool.false_eq_true, ite_false,
                          hA, hB, ha, hb, Option.bind_eq_bind, Option.bind_some]
                        change (if (classifyState candidate).val = .invalid then none else _) = _
                        rw [if_neg hnewvalid]
                        have hnRaw := hn
                        dsimp only [candidate] at hnRaw
                        simp only [Model.Operations.erasePaired, Model.Operations.insertPaired,
                          Arlib.Computation.Charged.val_opMany, ho, hnRaw,
                          Option.bind_eq_bind, Option.bind_some,
                          hneedProp, ite_true]
                      · exact congrArg Prod.fst hC
                    | some value =>
                      simp only [hC, Arlib.Computation.Charged.val_bind] at habort
                      split at habort <;> cases habort
                · rw [if_neg hneed] at habort
                  cases habort
