-- Prove2me | solution 1 for CountingMatroid.Analysis.FinitePhaseEstimationBound.completed_failure_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:26:59.22099+00:00
-- url     : https://prove2.me/submissions/f6ab4244-6b62-49cf-9cc6-697d01f1e774

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanLowerBound
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
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
import Theorems.Thm_CountingMatroid_Analysis_FiniteObservationMarkov_event_card_vectors
import Theorems.Thm_CountingMatroid_Analysis_FiniteObservationMarkov_finite_family_markov
import Theorems.Thm_CountingMatroid_Analysis_FinitePhaseEstimationBound_schedule_estimation_budget
import Theorems.Thm_CountingMatroid_Analysis_PhaseObservationExperiment_raw_means_iff_observation_data
import Theorems.Thm_CountingMatroid_Analysis_StationaryMeanLowerBound_observable_mean_lower

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
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
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.FinitePhaseEstimationBound
end CountingMatroid.Analysis.FinitePhaseEstimationBound
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteObservationMarkov

open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: A failed relative estimate whose mean is bounded below has
squared deviation at least the square of the corresponding absolute threshold.
TEXLINE: main.tex:1253-1266 -/
theorem relative_failure_square (η a mean estimate : ℚ)
    (hη : 0 < η) (ha : 0 < a) (hm : a ≤ mean)
    (hbad : ¬ RelativeEstimate η mean estimate) :
    (η * a) ^ 2 ≤ (estimate - mean) ^ 2 := by
  have hthreshold : 0 < η * a := mul_pos hη ha
  have hcompare : η * a ≤ η * mean := mul_le_mul_of_nonneg_left hm hη.le
  rcases not_and_or.mp hbad with hl | hu
  · have hleft : estimate < (1 - η) * mean := lt_of_not_ge hl
    have hdelta : estimate - mean < -(η * a) := by nlinarith
    nlinarith [sq_nonneg (estimate - mean + η * a)]
  · have hright : (1 + η) * mean < estimate := lt_of_not_ge hu
    have hdelta : η * a < estimate - mean := by nlinarith
    nlinarith [sq_nonneg (estimate - mean - η * a)]





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

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.PhaseObservationExperiment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.RelativeObservationBounds

















/-- INTERNAL: All the subprobability squared errors are nonnegative. -/
theorem observation_squared_error_nonneg {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (index : Observable n) :
    0 ≤ observationSquaredError r o₁ o₂ tape s j index := by
  classical
  unfold observationSquaredError
  split
  · exact le_rfl
  · split
    · exact sq_nonneg _
    · exact le_rfl



end CountingMatroid.Analysis.PhaseObservationExperiment

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.FinitePhaseEstimationBound
end CountingMatroid.Analysis.FinitePhaseEstimationBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FinitePhaseEstimationBound

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.FiniteObservationMarkov
open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: A conditional second-moment bound for each concrete observable
implies the finite-tape relative-error budget, retaining all completed
operational outputs and bounding aborts elsewhere.
TEXLINE: main.tex:1253-1266 -/
theorem solution (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (pref : List Bool)
    (hmoment : ∀ index : Observable n,
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
      (∑ suffix : List.Vector Bool t,
        observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
          (2 : ℚ) ^ t ≤ 40000 * (n : ℚ) ^ 8 / s.observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ 1 / (32 * ((s.L : ENNReal) + 1)) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  let tape := fun suffix : List Bool => fun i : ℕ => ((pref ++ suffix)[i]?).getD false
  let bad := fun suffix : List Bool => ObservationCompleted r o₁ o₂ (tape suffix) s j ∧
    ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂ (tape suffix) s j
  let error := fun (suffix : List.Vector Bool t) (index : Observable n) =>
    observationSquaredError r o₁ o₂ (tape suffix.val) s j index
  let a : ℚ := 1 / (20 * (n : ℚ) ^ 2)
  obtain ⟨hη, hN, hbudget⟩ := schedule_estimation_budget n p hn
  have ha : 0 < a := by dsimp only [a]; positivity
  have hbad : ∀ suffix : List.Vector Bool t, bad suffix.val →
      ∃ index, (s.η * a) ^ 2 ≤ error suffix index := by
    intro suffix hb
    obtain ⟨current, observed, hdata, hg, hobs⟩ := hb.1
    have hfail : ¬ ∀ index : Observable n,
        RelativeEstimate s.η (observableMean r o₁ o₂ s j current index)
          (empiricalMean s observed index) := by
      intro hall
      exact hb.2 ((raw_means_iff_observation_data _ _ _ _ _ _).mpr
        ⟨current, observed, hdata, hg, hobs, hall⟩)
    obtain ⟨index, hi⟩ := not_forall.mp hfail
    refine ⟨index, ?_⟩
    dsimp only [error]
    simp only [observationSquaredError, hdata, if_pos (And.intro hg hobs)]
    exact relative_failure_square s.η a _ _ hη ha
      (StationaryMeanLowerBound.observable_mean_lower n r o₁ o₂ p hn j current hg index) hi
  have hcard := finite_family_markov (fun suffix : List.Vector Bool t => bad suffix.val)
    error (1 / (2 : ℚ) ^ t) ((s.η * a) ^ 2)
    (40000 * (n : ℚ) ^ 8 / s.observations) (by positivity) (by positivity)
    (fun suffix index => observation_squared_error_nonneg _ _ _ _ _ _ _)
    hbad (by intro index; simpa only [div_eq_mul_inv, one_mul] using hmoment index)
  rw [← event_card_vectors t bad] at hcard
  have hrat : (Set.ncard {suffix : List Bool | suffix.length = t ∧ bad suffix} : ℚ) /
      (2 : ℚ) ^ t ≤ 1 / (32 * ((s.L : ℚ) + 1)) := by
    have hcard' := hcard.trans hbudget
    simpa only [div_eq_mul_inv, one_mul] using hcard'
  have hmass := ennreal_mass_of_rat_bound t
    (Set.ncard {suffix : List Bool | suffix.length = t ∧ bad suffix}) _ hrat
  have hrhs : ENNReal.ofReal ((1 / (32 * ((s.L : ℚ) + 1)) : ℚ) : ℝ) =
      1 / (32 * ((s.L : ENNReal) + 1)) := by
    push_cast
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.ofReal_mul, ENNReal.ofReal_add]
  rwa [hrhs] at hmass
