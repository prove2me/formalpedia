-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunResourceEnvelope.boundedRun_value_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:37:55.610913+00:00
-- url     : https://prove2.me/submissions/122a5644-c282-4d35-bac9-49a99ed03843

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_finishPhase_ratio_nonneg
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_numerator_nonneg

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
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight



/-- INTERNAL: A charged finite loop preserves any invariant preserved by its body. -/
theorem chargedFold_preserves {ι β : Type} (P : β → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b i, P b → P (f b i).val) (l : List ι) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f l b).val := by
  induction l generalizing b with
  | nil => simpa using hb
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih _ (hf b i hb)





















end CountingMatroid.Analysis.BoundedRunResourceEnvelope

end

section


/-!
Polynomial output encoding length is proved for every schedule and execution,
using additive observation heights and a phase-product invariant. Nonnegativity
and the zero-phase costs are also proved here. The complete resource envelope
uses separate oracle-call and nonoracle-work obligations; those dependencies
must be closed before the envelope has a complete proof.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The charged natural-power fold computes exponentiation. -/
private theorem natPower_fold_value (base : ℕ) (l : List ℕ) (acc : ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) l acc).val =
      acc * base ^ l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons _ xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih]
      simp [natMul, pow_succ]
      ring

/-- INTERNAL: The charged natural power loop computes exponentiation. -/
theorem natPower_value (base exponent : ℕ) :
    (CountingMatroid.Program.natPower base exponent).val = base ^ exponent := by
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  simpa using natPower_fold_value base (List.range exponent) 1


























open CountingMatroid.Analysis.RationalHeight





end CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · handoff blocked · the child-ready shell command was rejected because it used rm -f to remove the old response; no handoff was submitted and BoundedRunOtherSteps remains owned here.
* r16 · partial recovery · proved the all-phase output-length conjunct via rational height and phase-product induction; isolated nonoracle work in BoundedRunOtherSteps for live handoff.
* r15 · decomposed · separated the state-independent oracle charge into BoundedRunOracleCalls; output size and nonoracle charge still need a reachable-state invariant.
* r14 · partial recovery · proved observation type-count and phase-power charge bounds; the positive-phase rational-size and abort-path invariant remains open.
* r13 · partial recovery · proved phase-power binary length and a quadratic charge bound for rational multiplication; the reachable phase-state and abort-path cost invariant is still missing.
* r12 · open · verified that rational multiplication has unbounded charge on arbitrary input (`otherSteps (ratMul (2 ^ K : ℚ) 1) ≥ K`); a reachable-state invariant must also bound observation counts by the loop length.
* r11 · open · direct simplification exposed the entire positive-phase fold; the generic charged loop bound requires a price for arbitrary cursors, while rational-operation costs are unbounded without a reachable-state length invariant.
* r10 · open · audited arbitrary schedule fields and expanded the positive-phase goal; Arlib's fold cost bound needs a state-length invariant for the stored multiplier tables and phase accumulators, which is still absent.
* r9 · partial recovery · proved nonnegativity of every successful observation accumulator, completed phase ratio, and bounded-run output; the three positive-phase quantitative bounds still need a joint phase-state invariant.
* r8 · partial recovery · proved the zero-phase oracle and quadratic work bounds and integrated the entire zero-phase case into the envelope; the positive-phase joint invariant remains open.
* r7 · partial recovery · proved the charged natural-power value and isolated the zero-phase output; the positive-phase state-and-cost invariant remains open.
* r6 · open · isolated the capped-run phase invariant from schedule construction and amplification.
-/

end
/-!
Polynomial output encoding length is proved for every schedule and execution,
using additive observation heights and a phase-product invariant. Nonnegativity
and the zero-phase costs are also proved here. The complete resource envelope
uses separate oracle-call and nonoracle-work obligations; those dependencies
must be closed before the envelope has a complete proof.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: A successful bounded run has a nonnegative product of its phase ratios.
TEXLINE: main.tex:1430-1440 -/
theorem solution (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ) :
    0 ≤ (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 := by
  let P : Option (CountingMatroid.Program.AnnealingCursor n) → Prop :=
    fun acc => ∀ current, acc = some current → 0 ≤ current.product
  let f : ℕ → Option (CountingMatroid.Program.AnnealingCursor n) →
      Arlib.Computation.Charged Op Cell
        (Option (CountingMatroid.Program.AnnealingCursor n)) :=
    fun j acc =>
      match acc with
      | none => pure none
      | some current => do
          let q ← CountingMatroid.Program.ratPower s.ρ j
          let started ← CountingMatroid.Program.restartPhase r o₁ o₂ tape s
            current.tables j current.bitCursor
          match started with
          | none => pure none
          | some started =>
              let observed ← CountingMatroid.Program.observePhase r o₁ o₂ tape s q
                current.currentWeights started
              match observed with
              | none => pure none
              | some observed =>
                  let finished ← CountingMatroid.Program.finishPhase s j
                    current.currentWeights observed
                  match finished with
                  | none => pure none
                  | some (ratio, nextWeights) =>
                      let product ← ratMul current.product ratio
                      let next ← successor j
                      let update ← lessThan next s.L
                      if update then
                        let tables ← learnedWeightWrite current.tables next s.L nextWeights
                        pure (some ⟨tables, nextWeights, product, observed.bitCursor⟩)
                      else pure (some ⟨current.tables, nextWeights, product,
                        observed.bitCursor⟩)
  have hstep : ∀ acc j, P acc → P (f j acc).val := by
    intro acc j hacc next hnext
    cases acc with
    | none => simp [f] at hnext
    | some current =>
        dsimp [f] at hnext
        cases hstarted : (CountingMatroid.Program.restartPhase r o₁ o₂ tape s
          current.tables j current.bitCursor).val with
        | none => simp [hstarted] at hnext
        | some started =>
            simp only [hstarted, Arlib.Computation.Charged.val_bind] at hnext
            cases hobserved : (CountingMatroid.Program.observePhase r o₁ o₂ tape s
              (CountingMatroid.Program.ratPower s.ρ j).val current.currentWeights
              started).val with
            | none => simp [hobserved] at hnext
            | some observed =>
                simp only [hobserved, Arlib.Computation.Charged.val_bind] at hnext
                cases hfinished : (CountingMatroid.Program.finishPhase s j
                  current.currentWeights observed).val with
                | none => simp [hfinished] at hnext
                | some result =>
                    rcases result with ⟨ratio, nextWeights⟩
                    simp only [hfinished, Arlib.Computation.Charged.val_bind,
                      ratMul, Arlib.Computation.Charged.val_opMany] at hnext
                    have hratio := finishPhase_ratio_nonneg s j current.currentWeights
                      observed
                      (observePhase_numerator_nonneg r o₁ o₂ tape s
                        (CountingMatroid.Program.ratPower s.ρ j).val
                        current.currentWeights started hρ observed hobserved)
                      ratio nextWeights hfinished
                    split at hnext
                    · simp only [Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_pure,
                        learnedWeightWrite, Arlib.Computation.Charged.val_opMany] at hnext
                      cases Option.some.inj hnext
                      exact mul_nonneg (hacc current rfl) hratio
                    · simp only [Arlib.Computation.Charged.val_pure] at hnext
                      cases Option.some.inj hnext
                      exact mul_nonneg (hacc current rfl) hratio
  unfold CountingMatroid.Program.boundedRun
  simp only [Arlib.Computation.Charged.val_bind]
  unfold Arlib.Computation.Charged.repeatFor
  have hinit : P (some ⟨(allocateLearnedWeights n s.L (initialWeights n).val).val,
      (initialWeights n).val, 1, 0⟩) := by
    intro current hc
    cases Option.some.inj hc
    exact zero_le_one
  have hphases := chargedFold_preserves P (fun acc j => f j acc) hstep
    (List.range s.L) _ hinit
  split
  · simp
  · simp only [Arlib.Computation.Charged.val_bind, natPower_value,
      ratOfNat, ratMul, Arlib.Computation.Charged.val_opMany]
    exact mul_nonneg (by positivity) (hphases _ (by assumption))
