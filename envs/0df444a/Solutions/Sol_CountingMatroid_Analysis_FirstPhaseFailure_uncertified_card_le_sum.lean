-- Prove2me | solution 1 for CountingMatroid.Analysis.FirstPhaseFailure.uncertified_card_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:44:19.701883+00:00
-- url     : https://prove2.me/submissions/9a97a517-49ab-452a-9a48-21e02d93962a

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
set_option autoImplicit false

/-!
A local failure event for the actual charged phase prefixes. A certificate
requires completion, an accurate ratio, and good stored multipliers. First
failure events partition failure of these certificates, including aborts.
The per-phase finite-tape probability estimate remains in the consuming theorem;
it requires the paper's conditional restart and observation analysis and the
adaptive finite-tape coupling. No independence of adjacent phase events is
assumed by this representation.
-/

namespace CountingMatroid.Analysis.FirstPhaseFailure
end CountingMatroid.Analysis.FirstPhaseFailure
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FirstPhaseFailure

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase

/-- INTERNAL: Failure of the local certificates is covered by the first
failure events of the actual phase prefixes. This is a finite counting union
bound, and makes no independence assumption about adjacent phases.
TEXLINE: main.tex:1271-1285 -/
theorem solution (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (m : ℕ) :
    Set.ncard {bits : List Bool | bits.length = m ∧
      ¬ ∀ j < s.L, CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j} ≤
    ∑ j ∈ Finset.range s.L,
      Set.ncard {bits : List Bool | bits.length = m ∧
        FirstFailure r o₁ o₂ (fun i => (bits[i]?).getD false) s j} := by
  classical
  let bad := fun j => {bits : List Bool | bits.length = m ∧
    FirstFailure r o₁ o₂ (fun i => (bits[i]?).getD false) s j}
  let failures := ⋃ j ∈ Finset.range s.L, bad j
  have hsubset : {bits : List Bool | bits.length = m ∧
      ¬ ∀ j < s.L, CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j} ⊆
      failures := by
    intro bits hb
    have hex : ∃ j, j < s.L ∧
        ¬ CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j := by
      obtain ⟨j, hj⟩ := not_forall.mp hb.2
      obtain ⟨hj, hbad⟩ := not_forall.mp hj
      exact ⟨j, hj, hbad⟩
    let j := Nat.find hex
    have hj : j < s.L ∧
        ¬ CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j :=
      Nat.find_spec hex
    have hearlier : ∀ a < j,
        CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s a := by
      intro a ha
      by_contra hbad
      exact Nat.find_min hex ha ⟨ha.trans hj.1, hbad⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hj.1, ?_⟩⟩
    exact ⟨hb.1, hearlier, hj.2⟩
  have hfinite : failures.Finite :=
    (List.finite_length_eq Bool m).subset (by
      intro bits hb
      obtain ⟨j, hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨_, hb⟩ := Set.mem_iUnion.mp hb
      exact hb.1)
  exact (Set.ncard_le_ncard hsubset hfinite).trans
    ((Finset.range s.L).set_ncard_biUnion_le bad)
