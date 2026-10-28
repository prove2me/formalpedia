-- Prove2me | solution 1 for CountingMatroid.Analysis.ReturnAttemptTail.attempt_scan_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:31:50.050807+00:00
-- url     : https://prove2.me/submissions/92e9ff8c-a222-4f61-91e3-9827bd37523c

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_ReturnAttemptTail
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryReturnOccupation
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
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
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
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_chainStep_success_interval
import Theorems.Thm_CountingMatroid_Analysis_ChainStepNoninvalid_chainStep_noninvalid
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_next_bound

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
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
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass















/-- INTERNAL: Inclusion of finite-tape events increases their mass. -/
theorem fairMass_mono (head : List Bool) (t : ℕ) (E F : (ℕ → Bool) → Prop)
    (h : ∀ bits : List.Vector Bool t,
      E (finiteTape (head ++ bits.val)) → F (finiteTape (head ++ bits.val))) :
    fairMass head t E ≤ fairMass head t F := by
  classical
  apply Finset.sum_le_sum
  intro bits _
  by_cases he : E (finiteTape (head ++ bits.val))
  · simp only [he, h bits he, if_true, le_refl]
  · simp only [he, if_false]
    split_ifs <;> positivity





end CountingMatroid.Analysis.FiniteStoppedFiberMass

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The number of `chainStep` attempts made by one actual positive-time return,
as a value recursion. The instrumented return adds exactly this number to its
retained counter, including the attempt that ends in a draw abort. On a fresh
finite suffix whose every attempted step stays inside the block, the chance of
making more than m attempts is at most the ideal positive-time survival tail.
-/
namespace CountingMatroid.Analysis.ReturnAttemptTail

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open Arlib.Probability Arlib.MarkovChains











/-- INTERNAL: Tail weights are nonnegative. -/
theorem tailWeight_nonneg {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (A : Finset Ω) (m : ℕ) (x : Ω) : 0 ≤ tailWeight P A m x := by
  cases m with
  | zero => simp [tailWeight]
  | succ m =>
      exact Finset.sum_nonneg fun z _ => mul_nonneg (P.coe_nonneg x z) (survive_nonneg P A m z)

/-- INTERNAL: Off the target, positive-time survival is the tail weight. -/
theorem survive_eq_tailWeight {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (A : Finset Ω) (m : ℕ) (x : Ω) (hx : x ∉ A) :
    survive P A m x = tailWeight P A m x := by
  cases m with
  | zero => simp [tailWeight, hx]
  | succ m => rw [survive_succ_apply, if_neg hx]; rfl



/-- INTERNAL: Event mass on a fresh finite suffix is at most one. -/
theorem fairMass_le_one (head : List Bool) (t : ℕ) (E : (ℕ → Bool) → Prop) :
    fairMass head t E ≤ 1 := by
  classical
  unfold fairMass
  calc
    _ ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ)^t := by
      apply Finset.sum_le_sum
      intro bits _
      split_ifs
      · exact le_rfl
      · positivity
    _ = 1 := by simp [card_vector]



end CountingMatroid.Analysis.ReturnAttemptTail

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · per-return attempt recursion, exact retained-count identity for the instrumented return, occupation budget as tail sums, and the covered attempt-tail bound.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The number of `chainStep` attempts made by one actual positive-time return,
as a value recursion. The instrumented return adds exactly this number to its
retained counter, including the attempt that ends in a draw abort. On a fresh
finite suffix whose every attempted step stays inside the block, the chance of
making more than m attempts is at most the ideal positive-time survival tail.
-/
namespace CountingMatroid.Analysis.ReturnAttemptTail
end CountingMatroid.Analysis.ReturnAttemptTail
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ReturnAttemptTail

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open Arlib.Probability Arlib.MarkovChains

/-- INTERNAL: On a fresh finite suffix, a return whose attempted steps all stay
in the block makes more than m attempts with at most the ideal tail weight.
The invariant carries the deterministic bit budget between attempts.
TEXLINE: main.tex:1072-1087,1163-1176,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (P : FinChain (PairedSet n))
    (hstep : ∀ (head : List Bool) (t : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (chainStep r o₁ o₂ tape s.drawTrials q w x head.length).val = some (y, stop)) ≤ P x y)
    (Inv : RestartCursor n → Prop) (lim : ℕ)
    (hinv : ∀ (tape : ℕ → Bool) (current : RestartCursor n) (y : PairedSet n) (stop : ℕ),
      Inv current → current.attempts < s.restartCap →
      (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
        some (y, stop) →
      stop ≤ lim ∧ Inv ⟨y, stop, current.attempts + 1⟩)
    (k m : ℕ) (head : List Bool) (t : ℕ) (current : RestartCursor n)
    (hcursor : current.bitCursor = head.length) (hlim : head.length + t = lim)
    (hvalid : (classifyState current.state).val ≠ .invalid) (hcur : Inv current) :
    fairMass head t (fun tape => m + 1 ≤ attemptScan r o₁ o₂ tape s q w k current) ≤
      tailWeight P (Finset.univ.filter
        (fun x => (classifyState x).val = .transversal)) m current.state := by
  classical
  let A := Finset.univ.filter (fun x : PairedSet n => (classifyState x).val = .transversal)
  induction k generalizing m head t current with
  | zero =>
      have hz : fairMass head t
          (fun tape => m + 1 ≤ attemptScan r o₁ o₂ tape s q w 0 current) = 0 := by
        simp [fairMass, attemptScan]
      rw [hz]
      exact tailWeight_nonneg P A m current.state
  | succ k ih =>
    by_cases ha : current.attempts < s.restartCap
    · cases m with
      | zero => exact (fairMass_le_one _ _ _).trans_eq rfl
      | succ m =>
        let f := fun tape => (chainStep r o₁ o₂ tape s.drawTrials q w
          current.state head.length).val
        let E := fun tape (a : PairedSet n) (stop : ℕ) =>
          (classifyState a).val ≠ .transversal ∧
            m + 1 ≤ attemptScan r o₁ o₂ tape s q w k ⟨a, stop, current.attempts + 1⟩
        have hevent : ∀ bits : List.Vector Bool t,
            m + 1 + 1 ≤ attemptScan r o₁ o₂ (finiteTape (head ++ bits.val)) s q w (k+1)
              current →
            ∃ a, ∃ stop, stop ≤ head.length+t ∧
              f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
              E (finiteTape (head ++ bits.val)) a stop := by
          intro bits h
          simp only [attemptScan, ha, if_true, hcursor] at h
          cases hf : (chainStep r o₁ o₂ (finiteTape (head ++ bits.val)) s.drawTrials q w
              current.state head.length).val with
          | none => simp only [hf] at h; omega
          | some step =>
              simp only [hf] at h
              by_cases ht : (classifyState step.1).val = .transversal
              · simp only [ht, if_true] at h; omega
              · simp only [ht, if_false] at h
                have hb := hinv (finiteTape (head ++ bits.val)) current step.1 step.2 hcur ha
                  (by rw [hcursor]; exact hf)
                exact ⟨step.1, step.2, by omega, hf, ht, by omega⟩
        have hsum : fairMass head t
            (fun tape => m + 1 + 1 ≤ attemptScan r o₁ o₂ tape s q w (k+1) current) ≤
            ∑ a : PairedSet n, fairMass head t (fun tape => ∃ stop,
              stop ≤ head.length+t ∧ f tape = some (a,stop) ∧ E tape a stop) := by
          unfold fairMass
          rw [Finset.sum_comm]
          apply Finset.sum_le_sum
          intro bits _
          dsimp only
          split_ifs with h
          · obtain ⟨a, hs⟩ := hevent bits h
            apply le_trans (show (1 / (2 : ℝ)^t) ≤
              (if ∃ stop, stop ≤ head.length+t ∧
                f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
                E (finiteTape (head ++ bits.val)) a stop then 1 / (2 : ℝ)^t else 0) by
                  rw [if_pos hs])
            convert (Finset.single_le_sum (f := fun a =>
              if ∃ stop, stop ≤ head.length+t ∧
                f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
                E (finiteTape (head ++ bits.val)) a stop then 1 / (2 : ℝ)^t else 0)
              (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ a)) using 1
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> rfl
          · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
        apply hsum.trans
        change _ ≤ ∑ a : PairedSet n, P current.state a * survive P A m a
        apply Finset.sum_le_sum
        intro a _
        have hbound := FiniteStoppedFiberMass.stopped_next_bound head t f
          (ChainStepIntervalReplay.chainStep_success_interval r o₁ o₂ s.drawTrials q w
            current.state head.length) a (fun tape stop => E tape a stop)
          (survive P A m a) (survive_nonneg P A m a) (by
            intro stop hstart hstop pref hf
            have hpref : (head ++ pref.val).length = stop := by
              simp only [List.length_append, pref.2]
              omega
            by_cases ht : (classifyState a).val = .transversal
            · have hnone : ∀ tape, ¬ E tape a stop := fun tape h => h.1 ht
              simp only [fairMass, hnone, if_false, Finset.sum_const_zero]
              exact survive_nonneg P A m a
            · have hA : a ∉ A := by simp [A, ht]
              have hv := ChainStepNoninvalid.chainStep_noninvalid r o₁ o₂ _ s.drawTrials
                q w current.state head.length (a,stop) hvalid hf
              have hb := hinv (finiteTape (head ++ pref.val)) current a stop hcur ha
                (by rw [hcursor]; exact hf)
              have hi := ih m (head ++ pref.val) (t-(stop-head.length))
                ⟨a,stop,current.attempts+1⟩ hpref.symm (by rw [hpref]; omega) hv hb.2
              rw [survive_eq_tailWeight P A m a hA]
              refine le_trans (FiniteStoppedFiberMass.fairMass_mono _ _ _ _ ?_) hi
              intro bits h
              exact h.2)
        exact hbound.trans (mul_le_mul_of_nonneg_right
          (by simpa only [hcursor] using hstep head t current.state a hvalid)
          (survive_nonneg P A m a))
    · have hz : fairMass head t
          (fun tape => m + 1 ≤ attemptScan r o₁ o₂ tape s q w (k+1) current) = 0 := by
        simp [fairMass, attemptScan, ha]
      rw [hz]
      exact tailWeight_nonneg P A m current.state
