-- Prove2me | solution 1 for CountingMatroid.Analysis.AnnealingPartitionDrift.partition_step_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:11:18.758635+00:00
-- url     : https://prove2.me/submissions/999b568c-6f78-43a7-bb6f-d26767317e9d

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.AnnealingPartitionDrift

open CountingMatroid.Model



/-- INTERNAL: One cooling step bounds each power weight using only the
deficiency bound. No correctness theorem for the paired-rank scan is needed
because natural subtraction already bounds the deficiency by n.
TEXLINE: main.tex:1137-1145 -/
private theorem power_step_bounds (n j d : ℕ) (ρ : ℚ)
    (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1) (hhalf : (1 / 2 : ℚ) ≤ ρ ^ n)
    (hd : d ≤ n) :
    (ρ ^ j) ^ d / 2 ≤ (ρ ^ (j + 1)) ^ d ∧
      (ρ ^ (j + 1)) ^ d ≤ (ρ ^ j) ^ d := by
  have hdhalf : (1 / 2 : ℚ) ≤ ρ ^ d :=
    hhalf.trans (pow_le_pow_of_le_one hρ hρone hd)
  have hdone : ρ ^ d ≤ 1 := pow_le_one₀ hρ hρone
  have hbase : 0 ≤ (ρ ^ j) ^ d := pow_nonneg (pow_nonneg hρ _) _
  rw [pow_succ, mul_pow]
  constructor <;> nlinarith

/-- INTERNAL: Summing the same fixed class at adjacent parameters preserves
the per-state factor-two cooling bounds, including an empty class.
TEXLINE: main.tex:1141-1145 -/
private theorem class_partition_step {α : Type} [Fintype α]
    (n j : ℕ) (ρ : ℚ) (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (hhalf : (1 / 2 : ℚ) ≤ ρ ^ n) (d : α → ℕ)
    (hd : ∀ a, d a ≤ n) (inClass : α → Prop) [DecidablePred inClass] :
    let Z := fun k => ∑ a, if inClass a then (ρ ^ k) ^ d a else 0
    0 ≤ Z j ∧ Z j / 2 ≤ Z (j + 1) ∧ Z (j + 1) ≤ Z j := by
  classical
  dsimp only
  refine ⟨Finset.sum_nonneg (fun a _ => ?_), ?_, ?_⟩
  · split_ifs <;> positivity
  · rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : inClass a
    · simp only [if_pos ha]
      exact (power_step_bounds n j (d a) ρ hρ hρone hhalf (hd a)).1
    · simp [ha]
  · apply Finset.sum_le_sum
    intro a _
    by_cases ha : inClass a
    · simp only [if_pos ha]
      exact (power_step_bounds n j (d a) ρ hρ hρone hhalf (hd a)).2
    · simp [ha]







end CountingMatroid.Analysis.AnnealingPartitionDrift

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.AnnealingPartitionDrift
end CountingMatroid.Analysis.AnnealingPartitionDrift
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.AnnealingPartitionDrift

open CountingMatroid.Model

/-- PAPER: main.tex:1141-1145
Both the transversal partition sum and every ordered defect partition sum
decrease by a factor between one half and one at each schedule step. The
transversal sum is positive; the inequalities also retain empty defect classes. -/
theorem solution (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
    let D := fun a index => FirstPhaseFailure.defectPartition r o₁ o₂ (s.ρ ^ a) index
    0 < C j ∧ C j / 2 ≤ C (j + 1) ∧ C (j + 1) ≤ C j ∧
      ∀ index, 0 ≤ D j index ∧
        D j index / 2 ≤ D (j + 1) index ∧ D (j + 1) index ≤ D j index := by
  classical
  obtain ⟨hρ, hρone, hhalf⟩ := schedule_power_lower n p hn
  let ρ := (CountingMatroid.Interface.Pseudocode.setup n p).ρ
  have hC := class_partition_step n j ρ hρ.le hρone hhalf
    (TransversalPartition.transversalDeficiency r o₁ o₂)
    (fun _ => Nat.sub_le _ _) (fun _ => True)
  have hCpos : 0 < TransversalPartition.partitionSum r o₁ o₂ (ρ ^ j) := by
    unfold TransversalPartition.partitionSum
    apply Finset.sum_pos
    · intro A _
      exact pow_pos (pow_pos hρ _) _
    · exact Finset.univ_nonempty
  refine ⟨hCpos, ?_, ?_, ?_⟩
  · simpa only [if_true, TransversalPartition.partitionSum] using hC.2.1
  · simpa only [if_true, TransversalPartition.partitionSum] using hC.2.2
  · intro index
    exact class_partition_step n j ρ hρ.le hρone hhalf
      (fun state : PairedSet n => n -
        (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
      (fun _ => Nat.sub_le _ _)
      (fun state => (CountingMatroid.Program.classifyState state).val =
        .defect index.emptyPair index.fullPair)
