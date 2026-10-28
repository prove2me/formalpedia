-- Prove2me | solution 1 for CountingMatroid.Analysis.ResourceBound.estimate_none_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:43:25.157+00:00
-- url     : https://prove2.me/submissions/bf4df1be-d828-4bea-8c10-6160cce79728

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_boundedRun_resource_envelope
import Theorems.Thm_CountingMatroid_Analysis_ResourceBound_medianRational_nonneg
import Theorems.Thm_CountingMatroid_Analysis_ScheduleResourceEnvelope_schedule_resource_envelope

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.OutputSupport
end CountingMatroid.Analysis.OutputSupport
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations















/-- INTERNAL: The schedule envelope supplies the sign condition required by
the capped-run envelope. This is the nonnegative bounded-run output that the
estimator's median step will consume.
TEXLINE: main.tex:1350-1440 -/
theorem scheduled_boundedRun_nonneg (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → Bool) :
    0 ≤ (CountingMatroid.Program.boundedRun r o₁ o₂ tape
      (CountingMatroid.Program.schedule n p).val 0).val.1 := by
  obtain ⟨_, _, hschedule⟩ :=
    ScheduleResourceEnvelope.schedule_resource_envelope
  obtain ⟨_, _, hrun⟩ :=
    BoundedRunResourceEnvelope.boundedRun_resource_envelope
  exact (hrun n r o₁ o₂ tape (CountingMatroid.Program.schedule n p).val
    (hschedule n r p).1).1













end CountingMatroid.Analysis.ResourceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · closed the estimator cost and sign bound using the schedule and bounded-run envelopes and a proved median resource module.
* r7 · open · proved exact and bounded early-answer branches; reduced the estimator theorem to the `preprocess = none` branch, whose median scan still needs a rational-length cost invariant.
* r6 · open · split schedule arithmetic and capped-run rational invariants into independently elaborated resource envelopes; the estimator still needs median and charge composition.
* r5 · open · proved charged rational-power value and nonnegativity, and zero oracle calls for rational acceptance; the full polynomial bound still needs rational-size invariants.
* r4 · open · proved zero oracle cost for classification, bounded uniform draws, and paired selection, plus a `2*n` oracle cap for observation recording; rational-size invariants still block the full run bound.
* r3 · open · proved greedy and paired rank oracle caps and zero oracle cost of rational powers; the annealing phase still needs rational-size invariants.
* r2 · open · proved charged bind/loop and pretest resource lemmas; the annealing phase bound still needs rational-size invariants.
* r1 · open · proved support transport and added `r ≤ n`; the per-run charged polynomial bound remains unproved.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: Every observation in the estimator's median list is
nonnegative on the branch that enters annealing.
TEXLINE: main.tex:1430-1440 -/
theorem solution (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool)
    (h : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = none) :
    0 ≤ (CountingMatroid.Program.estimate contract.implementation
      n r o₁ o₂ p tape).val := by
  let s := (CountingMatroid.Program.schedule n p).val
  have hstep (j : ℕ) (acc : List ℚ) (hacc : ∀ q ∈ acc, 0 ≤ q) :
      ∀ q ∈ (do
        let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂
          (tape j) s 0
        consRational value acc).val, 0 ≤ q := by
    intro q hq
    simp only [Arlib.Computation.Charged.val_bind, consRational,
      Arlib.Computation.Charged.val_op] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact scheduled_boundedRun_nonneg n r o₁ o₂ p (tape j)
    · exact hacc q hq
  have hloop : ∀ (l : List ℕ) (acc : List ℚ),
      (∀ q ∈ acc, 0 ≤ q) →
      ∀ q ∈ (Arlib.Computation.Charged.foldl
        (fun acc j => do
          let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂
            (tape j) s 0
          consRational value acc) l acc).val, 0 ≤ q := by
    intro l
    induction l with
    | nil => intro acc hacc q hq; exact hacc q hq
    | cons j js ih =>
        intro acc hacc q hq
        rw [Arlib.Computation.Charged.val_foldl_cons] at hq
        exact ih _ (hstep j acc hacc) q hq
  have hmed := medianRational_nonneg
    (Arlib.Computation.Charged.repeatFor
      (fun j acc => do
        let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂
          (tape j) s 0
        consRational value acc) s.repetitions ([] : List ℚ)).val
    (by simpa [Arlib.Computation.Charged.repeatFor] using
      hloop (List.range s.repetitions) [] (by simp))
  simpa [CountingMatroid.Program.estimate, h, s] using hmed
