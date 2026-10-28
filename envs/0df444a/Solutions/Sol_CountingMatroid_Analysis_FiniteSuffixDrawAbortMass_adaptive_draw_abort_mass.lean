-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteSuffixDrawAbortMass.adaptive_draw_abort_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:32:15.529898+00:00
-- url     : https://prove2.me/submissions/dfaae485-9fa5-4b51-9d23-d38c89f2573f

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
import Theorems.Thm_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass_bounded_uniform_suffix_abort_mass
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_append_event_ncard
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_prefix_mass_le_one

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
section


set_option autoImplicit false

/-!
Finite fair-bit conditioning by a consumed prefix. Appending a fixed prefix
is a bijection on its suffix event; disjoint consumed-prefix cylinders let
uniform suffix estimates transfer to the whole finite tape. This module
proves only counting facts, not the program's stopping-prefix property or
the phase's conditional analytic estimate.
-/

namespace CountingMatroid.Analysis.FiniteTapePrefixBound





/-- INTERNAL: A fixed-prefix event has prefix mass times its fresh-suffix
mass under the finite uniform fair-bit law. This is the conditional-law
identity used before applying a uniform estimate for each successful history.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem append_event_mass (m : ℕ) (pref : List Bool)
    (hlen : pref.length ≤ m) (E : List Bool → Prop) :
    (Set.ncard {bits : List Bool | bits.length = m ∧ pref <+: bits ∧ E bits} :
      ENNReal) * (1 / 2 : ENNReal) ^ m =
    (1 / 2 : ENNReal) ^ pref.length *
      ((Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length)) := by
  rw [append_event_ncard m pref hlen E]
  have hp : (1 / 2 : ENNReal) ^ m =
      (1 / 2 : ENNReal) ^ pref.length * (1 / 2 : ENNReal) ^ (m - pref.length) := by
    rw [← Nat.add_sub_of_le hlen, pow_add]
    simp only [Nat.add_sub_cancel_left]
  rw [hp]
  ac_rfl









end CountingMatroid.Analysis.FiniteTapePrefixBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · proved · Boolean tape count, fixed-prefix event bijection and mass, stopping-prefix freeness, prefix-cylinder disjointness, total prefix mass bound, and transfer of uniform suffix bounds. These counting results are used by `FiniteTapeLowerTail`; actual successful-history replay and analytic phase bounds are separate obligations.
-/

end
set_option autoImplicit false

/-!
Finite fair-suffix rejection bounds for the actual charged integer sampler.
The single-call bound uses the proved forced-leading-bit count for covered
rejection trials. The prefix-cylinder transfer below separates this stochastic
bound from the program's reachability and finite-block coverage proof.
-/

namespace CountingMatroid.Analysis.FiniteSuffixDrawAbortMass
end CountingMatroid.Analysis.FiniteSuffixDrawAbortMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteTapePrefixBound

/-- INTERNAL: Prefix-free reached calls with covered rejection trials have
the same abort bound even when their positive denominators depend on the
consumed history. The event retains the original defaulted finite tape.
TEXLINE: main.tex:1417-1421 -/
theorem solution (pref : List Bool) (trials t : ℕ)
    (cover : DrawPrefixCover trials t) :
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      ∃ head ∈ cover.prefixes, head <+: suffix ∧
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          trials (cover.denominator head) (pref.length + head.length)).val.1 = none} :
      ENNReal) * (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal (((1 / 2 : ℚ) ^ trials : ℚ) : ℝ) := by
  classical
  let β := ENNReal.ofReal (((1 / 2 : ℚ) ^ trials : ℚ) : ℝ)
  let part := fun head => {suffix : List Bool | suffix.length = t ∧
    head <+: suffix ∧
    (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
      trials (cover.denominator head) (pref.length + head.length)).val.1 = none}
  have hlen (head : List Bool) (hh : head ∈ cover.prefixes) : head.length ≤ t :=
    (Nat.le_add_right _ _).trans (cover.covered head hh)
  have hevent : {suffix : List Bool | suffix.length = t ∧
      ∃ head ∈ cover.prefixes, head <+: suffix ∧
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          trials (cover.denominator head) (pref.length + head.length)).val.1 = none} =
      ⋃ head ∈ cover.prefixes, part head := by
    ext suffix
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, part]
    aesop
  have hpart (head : List Bool) (hh : head ∈ cover.prefixes) :
      (Set.ncard (part head) : ENNReal) * (1 / 2 : ENNReal) ^ t ≤
        (1 / 2 : ENNReal) ^ head.length * β := by
    rw [show (Set.ncard (part head) : ENNReal) * (1 / 2 : ENNReal) ^ t =
      (1 / 2 : ENNReal) ^ head.length *
        ((Set.ncard {tail : List Bool | tail.length = t - head.length ∧
          (boundedUniform (fun i => ((pref ++ (head ++ tail))[i]?).getD false)
            trials (cover.denominator head) (pref.length + head.length)).val.1 = none} :
            ENNReal) * (1 / 2 : ENNReal) ^ (t - head.length)) from
      append_event_mass t head (hlen head hh) (fun suffix =>
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          trials (cover.denominator head) (pref.length + head.length)).val.1 = none)]
    apply mul_le_mul_right _ _
    simpa only [List.append_assoc, List.length_append] using
      bounded_uniform_suffix_abort_mass (pref ++ head) trials
        (cover.denominator head) (t - head.length) (cover.positive head hh)
        (by have hc := cover.covered head hh; omega)
  rw [hevent]
  calc
    _ ≤ ((∑ head ∈ cover.prefixes, Set.ncard (part head) : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ t :=
      mul_le_mul_left (Nat.cast_le.mpr (cover.prefixes.set_ncard_biUnion_le part)) _
    _ = ∑ head ∈ cover.prefixes,
        (Set.ncard (part head) : ENNReal) * (1 / 2 : ENNReal) ^ t := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ ∑ head ∈ cover.prefixes, (1 / 2 : ENNReal) ^ head.length * β :=
      Finset.sum_le_sum (fun head hh => hpart head hh)
    _ = (∑ head ∈ cover.prefixes, (1 / 2 : ENNReal) ^ head.length) * β :=
      (Finset.sum_mul ..).symm
    _ ≤ 1 * β := mul_le_mul_left
      (prefix_mass_le_one t cover.prefixes hlen cover.prefix_free) β
    _ = β := one_mul β
