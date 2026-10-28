-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartDrawProbeReplay.probeStep_foldl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:43:49.059597+00:00
-- url     : https://prove2.me/submissions/7933c0dc-2614-4597-a9f5-ce3eaacdc835

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeReplay
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeScanReplay
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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
set_option autoImplicit false

/-!
Pre-draw replay for the concrete ordinal probe, independent of schedule
arithmetic, finite-prefix packaging, or probability. The probe's descriptor
depends only on the tape between the restart cursor and the descriptor's own
cursor, even though the counted state continues reading afterwards. The proof
packages a per-step replay contract (`ProbeStep`) — sticky capture, inert
death, silence past the ordinal, capture replay, and quiet whole-value replay
— shows it for one trace transition from the scan lemmas, and closes it under
the transition and stage folds.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeReplay
end CountingMatroid.Analysis.RestartDrawProbeReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartDrawProbeReplay
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartDrawProbe

/-- INTERNAL: A fold of probe steps satisfying the replay contract satisfies it. -/
theorem solution {X α : Type} (bc : X → ℕ) (ordinal : ℕ)
    (f : (ℕ → Bool) → (Option X × ℕ) × Option (ℕ × ℕ) → α →
      Arlib.Computation.Charged Op Cell ((Option X × ℕ) × Option (ℕ × ℕ)))
    (hf : ∀ a, ProbeStep bc ordinal (fun tape acc => (f tape acc a).val)) (xs : List α) :
    ProbeStep bc ordinal
      (fun tape acc => (Arlib.Computation.Charged.foldl (f tape) xs acc).val) := by
  induction xs with
  | nil =>
    refine ⟨fun _ _ _ h => h, fun _ _ => rfl, fun _ _ h1 h2 => ⟨h1, h2⟩, ?_, ?_⟩
    · intro cur count floor _ tape out h
      cases h
    · intro cur count floor hfl tape c count' h _
      simp only [Arlib.Computation.Charged.val_foldl_nil, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact ⟨hfl, fun _ _ => rfl⟩
  | cons a xs ih =>
    have ha := hf a
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro tape acc d h
      simp only [Arlib.Computation.Charged.val_foldl_cons]
      exact ih.sticky tape _ d (ha.sticky tape acc d h)
    · intro tape count
      simp only [Arlib.Computation.Charged.val_foldl_cons]
      rw [ha.dead tape count]
      exact ih.dead tape count
    · intro tape acc h1 h2
      simp only [Arlib.Computation.Charged.val_foldl_cons]
      have hm := ha.past tape acc h1 h2
      exact ih.past tape _ hm.1 hm.2
    · intro cur count floor hfl tape out h
      simp only [Arlib.Computation.Charged.val_foldl_cons] at h
      cases hmid : (f tape ((some cur, count), none) a).val with
      | mk mid1 obs =>
      obtain ⟨st, cnt⟩ := mid1
      cases obs with
      | some d =>
        have hd := ih.sticky tape ((st, cnt), some d) d rfl
        rw [hmid, hd] at h
        have hdo : d = out := Option.some.inj h
        subst hdo
        have hc := ha.capture cur count floor hfl tape d (by simp only [hmid])
        refine ⟨hc.1, fun other hagree => ?_⟩
        have ho := hc.2 other hagree
        simp only [Arlib.Computation.Charged.val_foldl_cons]
        exact ih.sticky other _ d ho
      | none =>
        cases st with
        | none =>
          rw [hmid, ih.dead] at h
          cases h
        | some c =>
          by_cases hcnt : ordinal < cnt
          · rw [hmid, (ih.past tape _ rfl hcnt).1] at h
            cases h
          · have hq := ha.quiet cur count floor hfl tape c cnt hmid (by omega)
            rw [hmid] at h
            have hr := ih.capture c cnt (bc c) (le_refl _) tape out h
            refine ⟨hq.1.trans hr.1, fun other hagree => ?_⟩
            have h1 := hq.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hr.1))
            have h2 := hr.2 other (fun i hlo hhi => hagree i (hq.1.trans hlo) hhi)
            simp only [Arlib.Computation.Charged.val_foldl_cons]
            rw [h1]
            exact h2
    · intro cur count floor hfl tape c count' h hle
      simp only [Arlib.Computation.Charged.val_foldl_cons] at h
      cases hmid : (f tape ((some cur, count), none) a).val with
      | mk mid1 obs =>
      obtain ⟨st, cnt⟩ := mid1
      cases obs with
      | some d =>
        have hd := ih.sticky tape ((st, cnt), some d) d rfl
        rw [hmid] at h
        rw [h] at hd
        cases hd
      | none =>
        cases st with
        | none =>
          rw [hmid, ih.dead] at h
          cases h
        | some c1 =>
          by_cases hcnt : ordinal < cnt
          · have hp := (ih.past tape ((some c1, cnt), none) rfl hcnt).2
            rw [← hmid, h] at hp
            exact absurd hle (by simpa using hp)
          · have hq := ha.quiet cur count floor hfl tape c1 cnt hmid (by omega)
            rw [hmid] at h
            have hr := ih.quiet c1 cnt (bc c1) (le_refl _) tape c count' h hle
            refine ⟨hq.1.trans hr.1, fun other hagree => ?_⟩
            have h1 := hq.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hr.1))
            have h2 := hr.2 other (fun i hlo hhi => hagree i (hq.1.trans hlo) hhi)
            simp only [Arlib.Computation.Charged.val_foldl_cons]
            rw [h1]
            exact h2
