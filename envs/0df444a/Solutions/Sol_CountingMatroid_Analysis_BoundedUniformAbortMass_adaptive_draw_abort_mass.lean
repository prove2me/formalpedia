-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformAbortMass.adaptive_draw_abort_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:30:07.234978+00:00
-- url     : https://prove2.me/submissions/44367b5d-4b84-403c-94d0-b640dbf01b76

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_boundedUniform_abort_mass
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_finite_prefix_failure_bound

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
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteObservationMarkov

open CountingMatroid.Analysis.RelativeObservationBounds







/-- INTERNAL: Convert a rational finite-tape mass estimate to ENNReal,
matching the cardinality normalization used by the lower-tail theorem.
TEXLINE: main.tex:1392-1427 -/
theorem ennreal_mass_of_rat_bound (t card : ℕ) (bound : ℚ)
    (h : (card : ℚ) / (2 : ℚ) ^ t ≤ bound) :
    (card : ENNReal) * (1 / 2 : ENNReal) ^ t ≤ ENNReal.ofReal bound := by
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ t),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat] at he
  simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, ENNReal.inv_pow] using he



end CountingMatroid.Analysis.FiniteObservationMarkov

end
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

/-- INTERNAL: A single adaptive draw has the same rejection-cap budget as a
fixed-denominator call: its stopping prefixes are disjoint, and the denominator
is fixed before its fresh trial bits are read. Coverage stays explicit.
TEXLINE: main.tex:1415-1421 -/
theorem solution (base : List Bool) (t trials : ℕ)
    (history : DrawHistory base t trials) :
    (Set.ncard {bits : List Bool | bits.length = t ∧ history.abortEvent bits} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ (1 / 2 : ENNReal) ^ trials := by
  classical
  apply FiniteTapePrefixBound.finite_prefix_failure_bound t history.prefixes
    history.abortEvent ((1 / 2 : ENNReal) ^ trials)
    history.length_le history.prefix_free
  · intro bits _ he
    obtain ⟨head, hm, hp, _⟩ := he
    exact ⟨head, hm, hp⟩
  · intro head hhead
    let E := {suffix : List Bool | suffix.length = t - head.length ∧
      (boundedUniform (fun i => (((base ++ head) ++ suffix)[i]?).getD false)
        trials (history.denominator head) (base ++ head).length).val.1 = none}
    have hsub : {suffix : List Bool | suffix.length = t - head.length ∧
        history.abortEvent (head ++ suffix)} ⊆ E := by
      intro suffix hs
      obtain ⟨other, hother, hp, habort⟩ := hs.2
      have heq : other = head := by
        rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append head suffix) with h | h
        · exact history.prefix_free other hother head hhead h
        · exact (history.prefix_free head hhead other hother h).symm
      subst other
      refine ⟨hs.1, ?_⟩
      simpa only [List.append_assoc, List.length_append] using habort
    have hfinite : E.Finite :=
      (List.finite_length_eq Bool (t - head.length)).subset (fun _ hs => hs.1)
    have hcard := Set.ncard_le_ncard hsub hfinite
    have hsingle := FiniteObservationMarkov.ennreal_mass_of_rat_bound
      (t - head.length) E.ncard ((1 / 2 : ℚ) ^ trials)
      (boundedUniform_abort_mass (base ++ head) trials (history.denominator head)
        (t - head.length) (history.positive head hhead) (history.coverage head hhead))
    have hhalf : ENNReal.ofReal (((1 / 2 : ℚ) ^ trials : ℚ) : ℝ) =
        (1 / 2 : ENNReal) ^ trials := by
      push_cast
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    rw [hhalf] at hsingle
    exact (mul_le_mul_left (Nat.cast_le.mpr hcard) _).trans hsingle
