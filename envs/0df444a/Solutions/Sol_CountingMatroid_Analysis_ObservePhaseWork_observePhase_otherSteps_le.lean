-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservePhaseWork.observePhase_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:48:36.146656+00:00
-- url     : https://prove2.me/submissions/c630ca4d-edee-4325-9c85-f0c41da67aa7

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
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_recordObservation_height_le
import Theorems.Thm_CountingMatroid_Analysis_ObservePhaseWork_recordObservation_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_chainStep_otherSteps_le

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false
namespace CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: A pure computation contributes no nonoracle work. -/
@[simp] theorem work_pure {α : Type} (x : α) :
    otherSteps (pure x : Arlib.Computation.Charged Op Cell α) = 0 := by
  simp [otherSteps]

/-- INTERNAL: One charged word instruction contributes one nonoracle step. -/
@[simp] theorem work_word {α : Type} (i : Arlib.Computation.Op) (x : α) :
    otherSteps (Arlib.Computation.Charged.op (Op.word i) x) = 1 := by
  cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.one]

/-- INTERNAL: A batch of word instructions contributes its batch length. -/
@[simp] theorem work_words {α : Type} (i : Arlib.Computation.Op) (k : ℕ) (x : α) :
    otherSteps (Arlib.Computation.Charged.opMany (Op.word i) k x) = k := by
  cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.many]























end CountingMatroid.Analysis.PhaseChainWork

end

section


set_option autoImplicit false
namespace CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.RationalHeight





/-- INTERNAL: Carry a growing size invariant through a finite charged loop,
charging a fixed budget only at states reached before the loop cap. -/
private theorem fold_work_growth {ι β : Type} (P : β → ℕ → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β) (N B : ℕ)
    (hf : ∀ b i k, k < N → P b k →
      otherSteps (f b i) ≤ B ∧ P (f b i).val (k + 1))
    (l : List ι) (b : β) (k : ℕ) (hk : k + l.length ≤ N) (hb : P b k) :
    otherSteps (Arlib.Computation.Charged.foldl f l b) ≤ l.length * B := by
  induction l generalizing b k with
  | nil => simp [otherSteps]
  | cons i l ih =>
      rw [show Arlib.Computation.Charged.foldl f (i :: l) b =
        f b i >>= fun next => Arlib.Computation.Charged.foldl f l next from rfl,
        otherSteps_bind]
      have hs := hf b i k (by simp only [List.length_cons] at hk; omega) hb
      have ht := ih (f b i).val (k + 1) (by simp only [List.length_cons] at hk; omega) hs.2
      simpa [List.length_cons, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hs.1 ht


end CountingMatroid.Analysis.ObservePhaseWork

end
set_option autoImplicit false
namespace CountingMatroid.Analysis.ObservePhaseWork
end CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: The observation loop's work is bounded using the reached
accumulator-height invariant, rather than a bound for arbitrary fold inputs.
TEXLINE: main.tex:1362-1378,1428-1439 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (observePhase r o₁ o₂ tape s q weights start) ≤
      n * n + 1 + s.observations *
        (1 + chainBudget n s.drawTrials K +
          recordBudget n (binaryRatLength s.ρ)
            (1 + s.observations * (4 + n * binaryRatLength s.ρ + 1))) := by
  let D := 4 + n * binaryRatLength s.ρ + 1
  let P : Option (ObservationCursor n) → ℕ → Prop :=
    fun acc k => ∀ next, acc = some next → rationalHeight next.numeratorSum ≤ 1 + k * D
  unfold observePhase
  rw [otherSteps_bind]
  simp only [allocateCounts, work_words]
  apply Nat.add_le_add_left
  unfold Arlib.Computation.Charged.repeatFor
  apply (fold_work_growth P _ s.observations
    (1 + chainBudget n s.drawTrials K +
      recordBudget n (binaryRatLength s.ρ) (1 + s.observations * D)) ?_
    (List.range s.observations) _ 0 (by simp) ?_).trans_eq (by simp [D])
  · intro acc index k hk hacc
    dsimp only
    cases acc with
    | none => simp [P]
    | some current =>
        have hcur := hacc current rfl
        have hg : rationalHeight current.numeratorSum ≤ 1 + s.observations * D := by
          have := Nat.mul_le_mul_right D (Nat.le_of_lt hk)
          omega
        have hrec := recordObservation_otherSteps_le r o₁ o₂ s.ρ current _ hg
        have hc := chainStep_otherSteps_le r o₁ o₂ tape s.drawTrials q weights
          current.state current.bitCursor K hq hw
        simp only [otherSteps_bind, Arlib.Computation.Charged.val_bind]
        split
        · constructor
          · simp [natEqual]; omega
          · intro next hn
            have hh := recordObservation_height_le r o₁ o₂ s.ρ current next hn
            have hone : binaryRatLength (1 : ℚ) = 4 := by decide
            dsimp [P, D] at *
            nlinarith
        · simp only [otherSteps_bind, Arlib.Computation.Charged.val_bind]
          split
          · constructor
            · simp [natEqual]; omega
            · simp [P]
          · rename_i state cursor he
            have hnrec := recordObservation_otherSteps_le r o₁ o₂ s.ρ
              ⟨state, cursor, current.counts, current.numeratorSum⟩ _ hg
            constructor
            · simp [natEqual]; omega
            · intro next hn
              have hh := recordObservation_height_le r o₁ o₂ s.ρ
                ⟨state, cursor, current.counts, current.numeratorSum⟩ next hn
              have hone : binaryRatLength (1 : ℚ) = 4 := by decide
              dsimp [P, D] at *
              nlinarith
  · intro next hn
    cases Option.some.inj hn
    norm_num [rationalHeight, Nat.log2_eq_log_two]
