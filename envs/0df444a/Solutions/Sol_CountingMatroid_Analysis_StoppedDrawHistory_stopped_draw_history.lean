-- Prove2me | solution 1 for CountingMatroid.Analysis.StoppedDrawHistory.stopped_draw_history
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:21:07.999932+00:00
-- url     : https://prove2.me/submissions/243cf7e9-f37c-4a07-93a8-0145b6c74c17

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
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_StoppedDrawHistory
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

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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
A deterministic stopping descriptor separates operational replay from the
finite prefix-free packaging required by the adaptive draw mass bound.
-/
namespace CountingMatroid.Analysis.StoppedDrawHistory
end CountingMatroid.Analysis.StoppedDrawHistory
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StoppedDrawHistory

/-- INTERNAL: Finite stopping descriptors produce covered prefix-free draw
histories, preserving every actual descriptor and its denominator.
TEXLINE: main.tex:1415-1421 -/
theorem solution (base : List Bool) (t trials : ℕ)
    (draw : StoppedDraw t trials) :
    ∃ history : BoundedUniformAbortMass.DrawHistory base t trials,
      ∀ bits head v, bits.length = t → draw.site bits = some (head, v) →
        head ∈ history.prefixes ∧ history.denominator head = v ∧ head <+: bits := by
  classical
  let P : Set (List Bool) := {head | ∃ bits, bits.length = t ∧
    ∃ v, draw.site bits = some (head, v)}
  have hfinite : P.Finite := by
    apply ((List.finite_length_eq Bool t).image
      (fun bits => ((draw.site bits).getD ([], 0)).1)).subset
    rintro head ⟨bits, hlen, v, hs⟩
    exact ⟨bits, hlen, by simp only [hs, Option.getD_some]⟩
  have hw (head : List Bool) (h : head ∈ P) :
      ∃ v, ∃ bits, bits.length = t ∧ draw.site bits = some (head, v) := by
    obtain ⟨bits, hlen, v, hs⟩ := h
    exact ⟨v, bits, hlen, hs⟩
  let den := fun head => if h : head ∈ P then Classical.choose (hw head h) else 1
  have hd (head : List Bool) (h : head ∈ P) :
      ∃ bits, bits.length = t ∧ draw.site bits = some (head, den head) := by
    dsimp only [den]
    rw [dif_pos h]
    exact Classical.choose_spec (hw head h)
  have heq (bits head : List Bool) (v : ℕ) (hlen : bits.length = t)
      (hs : draw.site bits = some (head, v)) : den head = v := by
    have hm : head ∈ P := ⟨bits, hlen, v, hs⟩
    obtain ⟨other, ho, hsite⟩ := hd head hm
    have hr := draw.stable other bits head (den head) ho hlen hsite
      (draw.isPrefix bits head v hlen hs)
    exact (Prod.mk.inj (Option.some.inj (hr.symm.trans hs))).2
  refine ⟨⟨hfinite.toFinset, den, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro head hm
    obtain ⟨bits, hlen, hs⟩ := hd head (hfinite.mem_toFinset.mp hm)
    exact draw.positive bits head (den head) hlen hs
  · intro head hm
    obtain ⟨bits, hlen, hs⟩ := hd head (hfinite.mem_toFinset.mp hm)
    exact (draw.isPrefix bits head (den head) hlen hs).length_le.trans_eq hlen
  · intro a ha b hb hab
    obtain ⟨bitsA, hA, hsA⟩ := hd a (hfinite.mem_toFinset.mp ha)
    obtain ⟨bitsB, hB, hsB⟩ := hd b (hfinite.mem_toFinset.mp hb)
    have hr := draw.stable bitsA bitsB a (den a) hA hB hsA
      (hab.trans (draw.isPrefix bitsB b (den b) hB hsB))
    exact (Prod.mk.inj (Option.some.inj (hr.symm.trans hsB))).1
  · intro head hm
    obtain ⟨bits, hlen, hs⟩ := hd head (hfinite.mem_toFinset.mp hm)
    exact draw.coverage bits head (den head) hlen hs
  · intro bits head v hlen hs
    exact ⟨hfinite.mem_toFinset.mpr ⟨bits, hlen, v, hs⟩,
      heq bits head v hlen hs, draw.isPrefix bits head v hlen hs⟩
