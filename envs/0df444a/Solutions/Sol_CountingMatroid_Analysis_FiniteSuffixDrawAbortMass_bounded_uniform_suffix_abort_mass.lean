-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteSuffixDrawAbortMass.bounded_uniform_suffix_abort_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:30:48.901099+00:00
-- url     : https://prove2.me/submissions/428875a6-4277-46c4-973f-38d994417bab

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_boundedUniform_abort_mass
import Theorems.Thm_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass_suffix_event_mass_le_one

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

/-- INTERNAL: A covered positive-denominator call of the actual charged
sampler fails with fair-suffix mass at most two to the negative trial cap.
The prefix fixes the entire previous history; the starting cursor is exactly
its length, and the coverage premise includes every rejection trial.
TEXLINE: main.tex:1392-1421 -/
theorem solution (pref : List Bool) (trials v t : ℕ)
    (hv : 0 < v) (hcoverage : trials * ((v - 1).log2 + 1) ≤ t) :
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
        trials v pref.length).val.1 = none} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal (((1 / 2 : ℚ) ^ trials : ℚ) : ℝ) := by
  classical
  by_cases hzero : trials = 0
  · subst trials
    simpa only [pow_zero, Rat.cast_one, ENNReal.ofReal_one] using
      suffix_event_mass_le_one t (fun suffix =>
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          0 v pref.length).val.1 = none)
  by_cases hone : v = 1
  · subst v
    simp [boundedUniform, Model.Operations.lessThan,
      Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_op,
      Arlib.Computation.Charged.val_pure]
  exact CountingMatroid.Analysis.FiniteObservationMarkov.ennreal_mass_of_rat_bound
    t _ ((1 / 2 : ℚ) ^ trials)
    (CountingMatroid.Analysis.BoundedUniformAbortMass.boundedUniform_abort_mass
      pref trials v t hv hcoverage)
