-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformAbortMass.abort_suffix_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:25:34.652975+00:00
-- url     : https://prove2.me/submissions/833aac70-b6d0-4371-aad6-df5f999590f0

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_abort_forces_leading_bits
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_forced_bits_card
import Theorems.Thm_CountingMatroid_Analysis_FiniteObservationMarkov_event_card_vectors

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
Finite-bit rejection-cap bounds for the actual charged integer sampler.
A rejected trial has a true leading bit: a false leading bit produces an
integer below the positive denominator. Distinct trials use disjoint words.
Coverage is an explicit premise here; obtaining it for adaptive calls in a
whole phase restart remains an obligation of the consuming analysis.
-/

namespace CountingMatroid.Analysis.BoundedUniformAbortMass
end CountingMatroid.Analysis.BoundedUniformAbortMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformAbortMass

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: In a covered finite suffix, exhausting all integer-draw trials
forces one distinct true coordinate per trial, giving a Boolean-cylinder count.
TEXLINE: main.tex:1392-1421 -/
theorem solution (pref : List Bool) (trials v t : ℕ)
    (hv : 2 ≤ v) (hcoverage : trials * ((v - 1).log2 + 1) ≤ t) :
    Set.ncard {suffix : List Bool | suffix.length = t ∧
      (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
        trials v pref.length).val.1 = none} ≤ 2 ^ (t - trials) := by
  classical
  let width := (v - 1).log2 + 1
  let site : Fin trials → Fin t := fun k => ⟨k.val * width, by
    have hk := k.isLt
    dsimp only [width] at *
    nlinarith⟩
  let forced := Finset.univ.image site
  have hinj : Function.Injective site := by
    intro a b h
    have heq : a.val * width = b.val * width := congrArg Fin.val h
    apply Fin.ext
    dsimp only [width] at heq
    nlinarith
  have hcard : forced.card = trials := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [FiniteObservationMarkov.event_card_vectors]
  have hbound := forced_bits_card t forced (fun suffix =>
    (boundedUniform (fun i => ((pref ++ suffix.val)[i]?).getD false)
      trials v pref.length).val.1 = none) (by
    intro suffix habort i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    have hbits := abort_forces_leading_bits
      (fun i => ((pref ++ suffix.val)[i]?).getD false)
      trials v pref.length hv habort k.val k.isLt
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hbits
    have hlt : k.val * width < suffix.val.length := by
      rw [suffix.property]
      exact (site k).isLt
    change suffix.val[k.val * width]?.getD false = true at hbits
    rw [List.getElem?_eq_getElem hlt, Option.getD_some] at hbits
    exact hbits)
  simpa only [hcard] using hbound
