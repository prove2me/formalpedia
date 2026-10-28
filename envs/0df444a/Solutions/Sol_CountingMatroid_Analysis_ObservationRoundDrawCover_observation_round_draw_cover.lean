-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservationRoundDrawCover.observation_round_draw_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:33:53.396999+00:00
-- url     : https://prove2.me/submissions/3f366b5e-7912-44ba-b0bb-33d44bb47e42

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
import Definitions.Def_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSiteCovered
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSites
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
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
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSiteCovered_observation_round_draw_site_covered
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_chainDrawSite_positive
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_observation_round_draw_sites
import Theorems.Thm_CountingMatroid_Analysis_StoppingDrawPrefixCover_stopping_draw_prefix_cover

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Analysis.SuccessfulPhaseReplay
end CountingMatroid.Analysis.SuccessfulPhaseReplay
namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
end CountingMatroid.Analysis.SinglePhaseIntervalReplay
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
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
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.ObservationRoundDrawCover
end CountingMatroid.Analysis.ObservationRoundDrawCover
namespace CountingMatroid.Analysis.StoppingDrawPrefixCover
end CountingMatroid.Analysis.StoppingDrawPrefixCover
namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
section


set_option autoImplicit false

/-!
The three stopped draw descriptors of one actual observation attempt. Each
descriptor records an absolute bit cursor and the actual draw denominator.
History, restart, and observation replay compose with the chain-level
stopped-draw replay and abort-attribution invariants. The independent
selector correctness proof is isolated in a child module; trial coverage remains
a separate quantitative obligation.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawCover
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment



end CountingMatroid.Analysis.ObservationRoundDrawCover

namespace CountingMatroid.Analysis.ObservationRoundDrawSites

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.ObservationRoundDrawCover



/-- INTERNAL: Composing a stopped draw with successful history and loop
prefixes preserves its positive denominator.
TEXLINE: main.tex:1392-1421 -/
theorem observationDrawSite_positive (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (pref : List Bool) (k : ℕ) (site : Fin 3) (suffix : List Bool)
    (d : ℕ × ℕ) (hn : 0 < n)
    (h : observationDrawSite n r o₁ o₂ p j pref k site suffix = some d) :
    0 < d.2 := by
  unfold observationDrawSite at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨current, hh, start, hs, reached, ho, h⟩ := h
  split at h
  · cases h
  · exact chainDrawSite_positive r o₁ o₂ _ _ _ _ _ _ site d hn h













end CountingMatroid.Analysis.ObservationRoundDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r28 · proved · closed observation_round_draw_sites with proved stopped-draw replay, sampler range, classifier weight, and selector correctness helpers; preserved the statement and every original import. Both live handoffs were mechanically rejected without diagnostic, so all child proofs were completed vertically.
* r28 · narrowed · after mechanical rejection of r28-observation-draw-sites-1 without diagnostic, proved the chain replay and abort-attribution children; isolated the remaining classifier-valid selection population/count bridge in ClassifiedStateSelection.
* r28 · composed · removed the parent’s local proof gaps by composing history, restart, observation and stopped-chain replay; attributed reached aborts using the independent chain abort helper. Both child statements elaborate; their chain-level proofs are prepared for the live OPEN handoff.
* r27 · decomposed · defined the three pre-draw stopping descriptors; attempted prefix replay and abort attribution, exposing the n-element-state/selection and stopping-locality obligations separately from trial coverage.
-/

end
set_option autoImplicit false

/-!
The operational boundary needed by the observation-abort union bound.
A reached failing round is represented by two prefixes of the actual
observation loop. The cover assembly is proved from the concrete stopping
site locality/abort-attribution and finite-block coverage obligations in the
support files. Those two support theorems remain open, so this file does
not yet establish the observation-abort bound without proof debt.
No stochastic conclusion is assumed here.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawCover
end CountingMatroid.Analysis.ObservationRoundDrawCover
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservationRoundDrawCover

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

/-- INTERNAL: Construct the three actual draw-site prefix families for one
reached failing observation round. This is an operational statement: its
families are prefix-free, their denominators positive, and every trial lies
inside the remaining suffix. A draw abort on the original tape covers each
round failure; classifier/selection failures must first be ruled out.
TEXLINE: main.tex:1177-1187,1382-1421 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (k : ℕ) (hk : k < (CountingMatroid.Interface.Pseudocode.setup n p).observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    ∃ covers : Fin 3 → DrawPrefixCover s.drawTrials t,
      ∀ suffix : List Bool, suffix.length = t →
        ReachedObservationRoundAbort n r o₁ o₂ p j pref k suffix →
        ∃ site : Fin 3, ∃ head ∈ (covers site).prefixes,
          head <+: suffix ∧
          (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
            s.drawTrials ((covers site).denominator head)
            (pref.length + head.length)).val.1 = none := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  obtain ⟨hlocal, habort⟩ :=
    ObservationRoundDrawSites.observation_round_draw_sites n r M₁ M₂ o₁ o₂ p
      hn hfull hr h₁ h₂ hpositive j hj pref hprefix k hk
  have hcoverage :=
    ObservationRoundDrawSiteCovered.observation_round_draw_site_covered n r M₁ M₂ o₁ o₂ p
      hn hfull hr h₁ h₂ hpositive j hj pref hprefix k hk
  let stop : Fin 3 → List Bool → Option (ℕ × ℕ) := fun site suffix =>
    (ObservationRoundDrawSites.observationDrawSite n r o₁ o₂ p j pref k site suffix).map
      (fun d => (d.1 - pref.length, d.2))
  have hbound (site : Fin 3) (suffix : List Bool) (hlen : suffix.length = t)
      (d : ℕ × ℕ) (hd : stop site suffix = some d) :
      0 < d.2 ∧ d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤ t := by
    obtain ⟨absolute, hsite, heq⟩ := Option.map_eq_some_iff.mp hd
    have hc := hcoverage site suffix hlen absolute hsite
    have hp := ObservationRoundDrawSites.observationDrawSite_positive n r o₁ o₂ p j
      pref k site suffix absolute hn hsite
    change (absolute.1 - pref.length, absolute.2) = d at heq
    subst d
    refine ⟨hp, ?_⟩
    dsimp only [s, t]
    omega
  have hstoplocal (site : Fin 3) (suffix : List Bool) (hlen : suffix.length = t)
      (d : ℕ × ℕ) (hd : stop site suffix = some d)
      (other : List Bool) (hother : other.length = t)
      (htake : suffix.take d.1 <+: other) : stop site other = some d := by
    obtain ⟨absolute, hsite, heq⟩ := Option.map_eq_some_iff.mp hd
    change (absolute.1 - pref.length, absolute.2) = d at heq
    subst d
    have heq' := hlocal site suffix hlen absolute hsite other hother htake
    simp only [stop, heq', Option.map_some]
  have hcoverExists (site : Fin 3) :=
    StoppingDrawPrefixCover.stopping_draw_prefix_cover s.drawTrials t (stop site)
      (hbound site) (hstoplocal site)
  choose covers hcovers using hcoverExists
  refine ⟨covers, ?_⟩
  intro suffix hlen hbad
  obtain ⟨site, d, hsite, hfailed⟩ := habort suffix hlen hbad
  have hstop : stop site suffix = some (d.1 - pref.length, d.2) := by
    simp only [stop, hsite, Option.map_some]
  obtain ⟨head, hhead, hprefixHead, hlength, hdenominator⟩ :=
    hcovers site suffix hlen (d.1 - pref.length, d.2) hstop
  have hc := hcoverage site suffix hlen d hsite
  refine ⟨site, head, hhead, hprefixHead, ?_⟩
  rw [hdenominator, hlength, Nat.add_sub_of_le hc.1]
  exact hfailed
