-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunPhase.phase_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:34:55.453992+00:00
-- url     : https://prove2.me/submissions/96d1d8c9-1072-4da6-ac79-617fa2d6e90a

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_finishPhase_ratio_length_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_counts_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_height_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_binary_length_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_fold_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_FinishPhaseWork_finishPhase_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_ObservePhaseWork_observePhase_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseWork_restartPhase_otherSteps_le

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
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model





/-- INTERNAL: Two component lengths bound the rational encoding length. -/
theorem binaryRatLength_le_height (q : ℚ) :
    binaryRatLength q ≤ 2 * rationalHeight q + 2 := by
  unfold rationalHeight binaryRatLength binaryNatLength
  omega




end CountingMatroid.Analysis.RationalHeight

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight













/-- INTERNAL: The charged rational product costs at most the square of the
operand encoding lengths. TEXLINE: main.tex:1384-1390 -/
theorem otherSteps_ratMul_le (a b : ℚ) :
    otherSteps (ratMul a b) ≤ (binaryRatLength a + binaryRatLength b) ^ 2 := by
  simp only [otherSteps, ratMul, Arlib.Computation.Charged.cost_opMany,
    Arlib.Computation.CostVec.many]
  simp [Arlib.Computation.Op.all, binaryRatLength, binaryNatLength]
  change ((a.num.natAbs.log2 + a.den.log2 + 3) +
    (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2 ≤ _
  apply Nat.pow_le_pow_left
  omega



/-- INTERNAL: The phase-power computation has polynomial nonoracle charge.
TEXLINE: main.tex:1384-1390 -/
theorem ratPower_otherSteps_le (q : ℚ) (j : ℕ) :
    otherSteps (CountingMatroid.Program.ratPower q j) ≤
      j * (binaryRatLength 1 + j * binaryRatLength q) ^ 2 := by
  unfold CountingMatroid.Program.ratPower Arlib.Computation.Charged.repeatFor
  simpa using ratPower_fold_otherSteps_le q 1 (List.range j)







end CountingMatroid.Analysis.BoundedRunResourceEnvelope

end

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


/-!
The full nonoracle-work bound for one bounded annealing phase follows from
proved capped-chain, restart, observation, and finishing cost bounds. Each
bound includes abort paths; the observation and finishing scans carry their
reached rational-size invariants. The explicit sum of these component budgets
is absorbed into `runSize ^ 40`, with the original theorem statement retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Analysis.FinishPhaseWork
open CountingMatroid.Analysis.RationalHeight





/-- INTERNAL: Absorb the explicit component polynomial into the prescribed
fortieth-power envelope. TEXLINE: main.tex:1348-1440 -/
private theorem phaseWorkBudget_le (S : ℕ) (hS : 5 ≤ S) :
    phaseWorkBudget S ≤ S ^ 40 := by
  have hpos : 0 < S := by omega
  have hp0 : S ^ 0 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp1 : S ^ 1 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp2 : S ^ 2 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp3 : S ^ 3 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp4 : S ^ 4 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp5 : S ^ 5 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp6 : S ^ 6 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp7 : S ^ 7 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp8 : S ^ 8 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp9 : S ^ 9 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp10 : S ^ 10 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp11 : S ^ 11 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp12 : S ^ 12 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp13 : S ^ 13 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp14 : S ^ 14 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp15 : S ^ 15 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp16 : S ^ 16 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp17 : S ^ 17 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp18 : S ^ 18 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp19 : S ^ 19 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp20 : S ^ 20 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp21 : S ^ 21 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp22 : S ^ 22 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp23 : S ^ 23 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp24 : S ^ 24 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp25 : S ^ 25 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp26 : S ^ 26 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  simp only [pow_zero, pow_one] at hp0 hp1
  have hpoly : phaseWorkBudget S ≤ 20000 * S ^ 26 := by
    unfold phaseWorkBudget phaseWorkSumBudget chainBudget recordBudget finishEntryBudget
    ring_nf
    omega
  have hconstant : 20000 ≤ S ^ 7 := by
    calc
      20000 ≤ 5 ^ 7 := by norm_num
      _ ≤ S ^ 7 := Nat.pow_le_pow_left hS 7
  calc
    phaseWorkBudget S ≤ 20000 * S ^ 26 := hpoly
    _ ≤ S ^ 7 * S ^ 26 := Nat.mul_le_mul_right _ hconstant
    _ = S ^ 33 := by rw [← pow_add]
    _ ≤ S ^ 40 := Nat.pow_le_pow_right hpos (by omega)


end CountingMatroid.Analysis.BoundedRunPhase

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · closed phase_otherSteps_le using proved upstream chain/restart/observation/finishing work lemmas and an explicit polynomial envelope; the earlier extraction blocker is resolved.
* current · blocked · confirmed the upstream cost decomposition and unpacked the input size invariant; existing power/count/height support is downstream of this file, and the uniform-fold probe loses the reached-accumulator size bound. No new proof debt was introduced.
-/

end
/-!
The full nonoracle-work bound for one bounded annealing phase follows from
proved capped-chain, restart, observation, and finishing cost bounds. Each
bound includes abort paths; the observation and finishing scans carry their
reached rational-size invariants. The explicit sum of these component budgets
is absorbed into `runSize ^ 40`, with the original theorem statement retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Analysis.FinishPhaseWork
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: Bound the full work of one phase from its input rational-size
invariant, including work spent before a rejected draw or zero-count abort.
The input invariant is essential: arbitrary cursor rationals have unbounded
encoding lengths. No conclusion of phase_preserves_size is assumed here.
TEXLINE: main.tex:1348-1440 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ)
    (j : ℕ) (hj : j < s.L) (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    otherSteps (boundedRunPhase r o₁ o₂ tape s j acc) ≤ (runSize n s) ^ 40 := by
  generalize hSdef : runSize n s = S at hacc ⊢
  have hparts : n ≤ S ∧ s.L ≤ S ∧ s.τ ≤ S ∧ s.restartCap ≤ S ∧
      s.observations ≤ S ∧ s.drawTrials ≤ S ∧ binaryRatLength s.ρ ≤ S := by
    rw [← hSdef]
    unfold runSize
    omega
  rcases hparts with ⟨hn, hL, hτ, hrestart, hobs, htrials, hρsize⟩
  have hS : 5 ≤ S := by
    have hρmin : 4 ≤ binaryRatLength s.ρ := by
      unfold binaryRatLength binaryNatLength
      omega
    rw [← hSdef]
    unfold runSize
    omega
  have hpos : 0 < S := by omega
  have hjS : j + 1 ≤ S := by omega
  have hjle : j ≤ S := by omega
  have hone : binaryRatLength (1 : ℚ) = 4 := by decide
  have h13 : S ≤ S ^ 3 := by
    simpa using Nat.pow_le_pow_right hpos (show 1 ≤ 3 by omega)
  have h03 : 1 ≤ S ^ 3 := by
    simpa using Nat.pow_le_pow_right hpos (show 0 ≤ 3 by omega)
  have hconstant : 9 ≤ S ^ 8 := by
    calc
      9 ≤ 5 ^ 8 := by norm_num
      _ ≤ S ^ 8 := Nat.pow_le_pow_left hS 8
  have hdom : 4 + S * (4 + S * S) ≤ S ^ 11 := by
    calc
      _ ≤ 9 * S ^ 3 := by nlinarith
      _ ≤ S ^ 8 * S ^ 3 := Nat.mul_le_mul_right _ hconstant
      _ = S ^ 11 := by rw [← pow_add]
  have hqbudget : binaryRatLength 1 + n *
      (binaryRatLength 1 + j * binaryRatLength s.ρ) ≤ S ^ 11 := by
    apply (show binaryRatLength 1 + n *
        (binaryRatLength 1 + j * binaryRatLength s.ρ) ≤
        4 + S * (4 + S * S) by rw [hone]; gcongr <;> first | assumption | omega).trans hdom
  have hlinear : (j + 1) * S ^ 10 ≤ S ^ 11 := by
    calc
      _ ≤ S * S ^ 10 := Nat.mul_le_mul_right _ hjS
      _ = S ^ 11 := by ring
  cases acc with
  | none => simp [boundedRunPhase, otherSteps]
  | some current =>
      rcases hacc current rfl with ⟨hweights, htables, hproduct⟩
      have hw : ∀ index, binaryRatLength (current.currentWeights index) ≤ S ^ 11 :=
        fun i => (hweights i).trans hlinear
      have ht : ∀ phase index, binaryRatLength (current.tables phase index) ≤ S ^ 11 :=
        fun p i => (htables p i).trans hlinear
      have hp : binaryRatLength current.product ≤ S ^ 11 := hproduct.trans hlinear
      let powerCost := S * (4 + S * S) ^ 2
      let restartCost := S * (2 * S + 3) + S *
        (1 + S * (4 + S * S) ^ 2 + (S * S * S + 1) +
          S * (S * (chainBudget S S (S ^ 11) + S * (4 * S + 3) + 3)))
      let observeCost := S * S + 1 + S *
        (1 + chainBudget S S (S ^ 11) +
          recordBudget S S (1 + S * (4 + S * S + 1)))
      let finishCost := S * S + 5 + 2 * (S + 4) + 4 * (S + 4) ^ 2 +
        2 * (phaseWorkSumBudget S + 3 * (S + 4)) ^ 2 +
        S * S * finishEntryBudget S (S + 4)
          (S ^ 11 + S * S * (4 * (S + 4)) + S * (4 * (S + 4)))
      let productCost := (S ^ 11 + phaseWorkSumBudget S + 3 * (S + 4)) ^ 2
      let extraCost := 2 + S * S * S + 1
      have hpower : otherSteps (ratPower s.ρ j) ≤ powerCost := by
        apply (ratPower_otherSteps_le s.ρ j).trans
        dsimp only [powerCost]
        rw [hone]
        gcongr <;> first | assumption | omega
      have hstart : otherSteps (restartPhase r o₁ o₂ tape s current.tables j
          current.bitCursor) ≤ restartCost := by
        apply (restartPhase_otherSteps_le r o₁ o₂ tape s current.tables j
          current.bitCursor (S ^ 11) hqbudget ht).trans
        dsimp only [restartCost]
        rw [hone]
        unfold chainBudget
        gcongr <;> first | assumption | omega
      have hq : binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ j).val ≤ S ^ 11 := by
        have := ratPower_binary_length_le s.ρ j
        exact (Nat.add_le_add_left (Nat.mul_le_mul_left n this) _).trans hqbudget
      have hobserve (started : PairedSet n × ℕ) :
          otherSteps (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
            current.currentWeights started) ≤ observeCost := by
        apply (observePhase_otherSteps_le r o₁ o₂ tape s (ratPower s.ρ j).val
          current.currentWeights started (S ^ 11) hq hw).trans
        dsimp only [observeCost]
        unfold chainBudget recordBudget
        gcongr <;> first | assumption | omega
      have hsum (started : PairedSet n × ℕ) (observed : ObservationCursor n)
          (ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
            current.currentWeights started).val = some observed) :
          binaryRatLength observed.numeratorSum ≤ phaseWorkSumBudget S := by
        have hh := observePhase_height_le r o₁ o₂ tape s (ratPower s.ρ j).val
          current.currentWeights started observed ho
        have hb := binaryRatLength_le_height observed.numeratorSum
        apply (hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hh) _)).trans
        unfold phaseWorkSumBudget
        rw [hone]
        gcongr <;> first | assumption | omega
      have hfinish (started : PairedSet n × ℕ) (observed : ObservationCursor n)
          (ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
            current.currentWeights started).val = some observed) :
          otherSteps (finishPhase s j current.currentWeights observed) ≤ finishCost := by
        have hc := observePhase_counts_le r o₁ o₂ tape s (ratPower s.ρ j).val
          current.currentWeights started observed ho
        have hs := hsum started observed ho
        apply (finishPhase_otherSteps_le s j (S ^ 11) current.currentWeights
          observed hc hw).trans
        dsimp only [finishCost]
        unfold finishEntryBudget
        gcongr <;> first | assumption | omega
      have hmul (started : PairedSet n × ℕ) (observed : ObservationCursor n)
          (ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
            current.currentWeights started).val = some observed)
          (ratio : ℚ) (nextWeights : Multipliers n)
          (hf : (finishPhase s j current.currentWeights observed).val = some (ratio, nextWeights)) :
          otherSteps (ratMul current.product ratio) ≤ productCost := by
        have hc := observePhase_counts_le r o₁ o₂ tape s (ratPower s.ρ j).val
          current.currentWeights started observed ho
        have hs := hsum started observed ho
        have hr := finishPhase_ratio_length_le s j current.currentWeights observed
          (hc .transversal) ratio nextWeights hf
        apply (otherSteps_ratMul_le current.product ratio).trans
        dsimp only [productCost]
        apply Nat.pow_le_pow_left _ 2
        omega
      apply (show otherSteps (boundedRunPhase r o₁ o₂ tape s j (some current)) ≤
        phaseWorkBudget S from ?_).trans (phaseWorkBudget_le S hS)
      change otherSteps (boundedRunPhase r o₁ o₂ tape s j (some current)) ≤
        powerCost + restartCost + observeCost + finishCost + productCost + extraCost
      unfold boundedRunPhase
      rw [otherSteps_bind, otherSteps_bind]
      cases heStart : (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val with
      | none => simp only [heStart, work_pure, Nat.add_zero]; omega
      | some started =>
          simp only [heStart]
          rw [otherSteps_bind]
          have hoCost := hobserve started
          cases heObs : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
              current.currentWeights started).val with
          | none => simp only [heObs, work_pure, Nat.add_zero]; omega
          | some observed =>
              simp only [heObs]
              rw [otherSteps_bind]
              have hfCost := hfinish started observed heObs
              cases heFinish : (finishPhase s j current.currentWeights observed).val with
              | none => simp only [heFinish, work_pure, Nat.add_zero]; omega
              | some finished =>
                  rcases finished with ⟨ratio, nextWeights⟩
                  have hmCost := hmul started observed heObs ratio nextWeights heFinish
                  simp only [heFinish, otherSteps_bind]
                  split
                  · simp only [otherSteps_bind, work_pure, Nat.add_zero, successor,
                      lessThan, learnedWeightWrite, work_word, work_words]
                    have htable : s.L * n * n + 1 ≤ S * S * S + 1 := by gcongr
                    dsimp only [extraCost]
                    omega
                  · simp only [work_pure, Nat.add_zero, successor, lessThan, work_word]
                    dsimp only [extraCost]
                    omega
