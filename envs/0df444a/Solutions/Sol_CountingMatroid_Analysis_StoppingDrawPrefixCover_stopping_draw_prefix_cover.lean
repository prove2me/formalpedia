-- Prove2me | solution 1 for CountingMatroid.Analysis.StoppingDrawPrefixCover.stopping_draw_prefix_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:15:56.602886+00:00
-- url     : https://prove2.me/submissions/724fd8eb-fc5e-4494-93d9-577dbd5adc09

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
import Definitions.Def_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
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
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
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

namespace CountingMatroid.Analysis.StoppingDrawPrefixCover
end CountingMatroid.Analysis.StoppingDrawPrefixCover
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

/-!
Construct a draw cover from a deterministic stopped draw descriptor. A
descriptor records the consumed suffix length and denominator. Locality of
the stopped descriptor, positivity, and trial coverage are explicit premises;
no program reachability or quantitative bit-length assertion is assumed.
-/

namespace CountingMatroid.Analysis.StoppingDrawPrefixCover
end CountingMatroid.Analysis.StoppingDrawPrefixCover
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StoppingDrawPrefixCover

open CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

/-- INTERNAL: Covered deterministic draw stops yield a prefix-free cover,
with its denominator recovered by completing each head with false bits.
TEXLINE: main.tex:1392-1421 -/
theorem solution (trials t : ℕ)
    (stop : List Bool → Option (ℕ × ℕ))
    (hbound : ∀ bits, bits.length = t → ∀ d, stop bits = some d →
      0 < d.2 ∧ d.1 + trials * ((d.2 - 1).log2 + 1) ≤ t)
    (hlocal : ∀ bits, bits.length = t → ∀ d, stop bits = some d →
      ∀ other, other.length = t → bits.take d.1 <+: other → stop other = some d) :
    ∃ cover : DrawPrefixCover trials t,
      ∀ bits, bits.length = t → ∀ d, stop bits = some d →
        ∃ head ∈ cover.prefixes, head <+: bits ∧
          head.length = d.1 ∧ cover.denominator head = d.2 := by
  classical
  let S := (List.finite_length_eq Bool t).toFinset
  let P : Finset (List Bool) := S.biUnion fun bits =>
    match stop bits with
    | none => ∅
    | some d => {bits.take d.1}
  have hmem (head : List Bool) : head ∈ P ↔
      ∃ bits, bits.length = t ∧ ∃ d, stop bits = some d ∧ head = bits.take d.1 := by
    simp only [P, Finset.mem_biUnion, S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨bits, hb, hh⟩
      cases hs : stop bits with
      | none => simp only [hs, Finset.notMem_empty] at hh
      | some d =>
          simp only [hs, Finset.mem_singleton] at hh
          exact ⟨bits, hb, d, hs, hh⟩
    · rintro ⟨bits, hb, d, hs, rfl⟩
      exact ⟨bits, hb, by simp only [hs, Finset.mem_singleton]⟩
  let denominator : List Bool → ℕ := fun head =>
    ((stop (head ++ List.replicate (t - head.length) false)).getD (0, 1)).2
  have hhead (bits : List Bool) (hb : bits.length = t) (d : ℕ × ℕ)
      (hs : stop bits = some d) :
      (bits.take d.1).length = d.1 ∧ denominator (bits.take d.1) = d.2 := by
    have hwidth := (hbound bits hb d hs).2
    have hle : d.1 ≤ t := by omega
    have hlen : (bits.take d.1).length = d.1 := by
      rw [List.length_take, hb, Nat.min_eq_left hle]
    refine ⟨hlen, ?_⟩
    have hcompletion : stop (bits.take d.1 ++
        List.replicate (t - (bits.take d.1).length) false) = some d :=
      hlocal bits hb d hs _ (by simp only [List.length_append,
        List.length_replicate, hlen]; omega) (List.prefix_append _ _)
    simp only [denominator, hcompletion, Option.getD_some]
  have hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b := by
    intro a ha b hb hab
    obtain ⟨bitsA, hA, dA, hsA, rfl⟩ := (hmem a).mp ha
    obtain ⟨bitsB, hB, dB, hsB, rfl⟩ := (hmem b).mp hb
    have heq := hlocal bitsA hA dA hsA bitsB hB
      (hab.trans (List.take_prefix _ _))
    have hd : dA = dB := Option.some.inj (heq.symm.trans hsB)
    subst dB
    exact hab.eq_of_length ((hhead bitsA hA dA hsA).1.trans
      (hhead bitsB hB dA hsB).1.symm)
  refine ⟨⟨P, denominator, ?_, ?_, hfree⟩, ?_⟩
  · intro head hh
    obtain ⟨bits, hb, d, hs, rfl⟩ := (hmem head).mp hh
    rw [(hhead bits hb d hs).2]
    exact (hbound bits hb d hs).1
  · intro head hh
    obtain ⟨bits, hb, d, hs, rfl⟩ := (hmem head).mp hh
    rw [(hhead bits hb d hs).1, (hhead bits hb d hs).2]
    exact (hbound bits hb d hs).2
  · intro bits hb d hs
    refine ⟨bits.take d.1, (hmem _).mpr ⟨bits, hb, d, hs, rfl⟩,
      List.take_prefix _ _, ?_⟩
    exact hhead bits hb d hs
