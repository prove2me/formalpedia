-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunOtherSteps.boundedRun_otherSteps_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:39:18.100039+00:00
-- url     : https://prove2.me/submissions/2bbe83b8-3b8c-482c-aa0e-25259244c38e

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunOtherSteps_finalization_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunOtherSteps_phaseFold_work_and_size

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
set_option autoImplicit false

/-!
The bounded-run nonoracle-work envelope is reduced to two single-phase
obligations: `phase_preserves_size` and `phase_otherSteps_le`. Their files
record the remaining multiplier-size and abort-path work proofs.

This module combines those statements by induction over the actual indexed
phase loop, bounds initialization, and proves the final-scaling work bound.
The full envelope is conditional on those two open child obligations; it is
not yet a completed resource proof. Existing power/count/height support is
still downstream in `BoundedRunResourceEnvelope` and needs upstream extraction
for use in the child proofs.
-/

namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: Isolate the nonoracle-work conjunct of the run resource envelope.
The size includes every schedule field used to determine loop caps or rational
operands, and the bound includes all abort paths.
TEXLINE: main.tex:1348-1440 -/
theorem solution :
    ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
      (s : AnnealingSchedule), 0 ≤ s.ρ →
      let size := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      otherSteps (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) ≤
        100 * size ^ 100 := by
  intro n r o₁ o₂ tape s hρ
  let S := runSize n s
  have hS : 5 ≤ S := by
    dsimp [S, runSize, binaryRatLength, binaryNatLength]
    omega
  have hS1 : 1 ≤ S := by omega
  have hn : n ≤ S := by dsimp [S, runSize]; omega
  have hL : s.L ≤ S := by dsimp [S, runSize]; omega
  have hL1 : s.L + 1 ≤ S := by dsimp [S, runSize]; omega
  have h6 : 6 ≤ S ^ 10 := by
    have h := Nat.pow_le_pow_left hS 10
    norm_num at h
    omega
  let initial : AnnealingCursor n :=
    ⟨(allocateLearnedWeights n s.L (initialWeights n).val).val,
      (initialWeights n).val, 1, 0⟩
  have hinit : PhaseSizeInvariant S 0 (some initial) := by
    intro current hcurrent
    cases Option.some.inj hcurrent
    dsimp [initial, initialWeights, allocateLearnedWeights]
    simp only [Nat.one_mul]
    change (∀ _ : DefectIndex n, binaryRatLength (4 : ℚ) ≤ S ^ 10) ∧
      (∀ (_ : ℕ) (_ : DefectIndex n), binaryRatLength (4 : ℚ) ≤ S ^ 10) ∧
      binaryRatLength (1 : ℚ) ≤ S ^ 10
    have hfour : binaryRatLength (4 : ℚ) = 6 := by decide
    have hone : binaryRatLength (1 : ℚ) = 4 := by decide
    rw [hfour, hone]
    exact ⟨fun _ => h6, fun _ _ => h6, by omega⟩
  let scan := Arlib.Computation.Charged.repeatFor
    (boundedRunPhase r o₁ o₂ tape s) s.L (some initial)
  have hscan : otherSteps scan ≤ s.L * S ^ 40 ∧
      PhaseSizeInvariant S s.L scan.val := by
    simpa [scan, Arlib.Computation.Charged.repeatFor, List.range_eq_range'] using
      phaseFold_work_and_size r o₁ o₂ tape s hρ s.L 0 (by omega) (some initial) hinit
  have hprod : ∀ current, scan.val = some current →
      binaryRatLength current.product ≤ S ^ 11 := by
    intro current hc
    have hp := (hscan.2 current hc).2.2
    calc
      binaryRatLength current.product ≤ (s.L + 1) * S ^ 10 := hp
      _ ≤ S * S ^ 10 := Nat.mul_le_mul_right _ hL1
      _ = S ^ 11 := by ring
  have hfinal := finalization_otherSteps_le scan.val (S ^ 11) hprod
  have hpow (k : ℕ) (hk : k ≤ 100) : S ^ k ≤ S ^ 100 :=
    Nat.pow_le_pow_right hS1 hk
  have hquad : n * n + 1 ≤ 2 * S ^ 2 := by
    have hnn := Nat.mul_le_mul hn hn
    have hone : 1 ≤ S ^ 2 := one_le_pow₀ hS1
    nlinarith only [hnn, hone]
  have hi : n * n + 1 ≤ 2 * S ^ 100 :=
    hquad.trans (Nat.mul_le_mul_left 2 (hpow 2 (by omega)))
  have ha : s.L * (n * n + 1) ≤ 2 * S ^ 100 := by
    calc
      s.L * (n * n + 1) ≤ S * (2 * S ^ 2) := Nat.mul_le_mul hL hquad
      _ = 2 * S ^ 3 := by ring
      _ ≤ 2 * S ^ 100 := Nat.mul_le_mul_left 2 (hpow 3 (by omega))
  have hs : otherSteps scan ≤ S ^ 100 := by
    calc
      otherSteps scan ≤ s.L * S ^ 40 := hscan.1
      _ ≤ S * S ^ 40 := Nat.mul_le_mul_right _ hL
      _ = S ^ 41 := by ring
      _ ≤ S ^ 100 := hpow 41 (by omega)
  have hf : 3 * n + 1 + (2 * n + 4 + S ^ 11) ^ 2 ≤ 53 * S ^ 100 := by
    have h11 : S ≤ S ^ 11 := Nat.le_self_pow (by decide) S
    have h22 : S ≤ S ^ 22 := Nat.le_self_pow (by decide) S
    have hone : 1 ≤ S ^ 11 := one_le_pow₀ hS1
    have hb : 2 * n + 4 + S ^ 11 ≤ 7 * S ^ 11 := by omega
    have hsq := Nat.pow_le_pow_left hb 2
    have heq : (7 * S ^ 11) ^ 2 = 49 * S ^ 22 := by ring
    rw [heq] at hsq
    calc
      3 * n + 1 + (2 * n + 4 + S ^ 11) ^ 2 ≤ 53 * S ^ 22 := by omega
      _ ≤ 53 * S ^ 100 := Nat.mul_le_mul_left 53 (hpow 22 (by omega))
  have hiCost : otherSteps (initialWeights n) = n * n + 1 := by
    simp [otherSteps, initialWeights, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  have haCost : otherSteps (allocateLearnedWeights n s.L (initialWeights n).val) =
      s.L * (n * n + 1) := by
    simp [otherSteps, allocateLearnedWeights, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  change otherSteps (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) ≤ 100 * S ^ 100
  unfold CountingMatroid.Program.boundedRun
  rw [otherSteps_bind, otherSteps_bind, otherSteps_bind]
  change otherSteps (initialWeights n) +
    (otherSteps (allocateLearnedWeights n s.L (initialWeights n).val) +
      (otherSteps scan + otherSteps (match scan.val with
        | none => pure ((0 : ℚ), (0 : ℕ))
        | some current => do
            let powerOfTwo ← natPower 2 n
            let scale ← ratOfNat powerOfTwo
            let estimate ← ratMul scale current.product
            pure (estimate, current.bitCursor)))) ≤ 100 * S ^ 100
  rw [hiCost, haCost]
  calc
    _ ≤ 2 * S ^ 100 + (2 * S ^ 100 + (S ^ 100 + 53 * S ^ 100)) :=
      Nat.add_le_add hi (Nat.add_le_add ha (Nat.add_le_add hs (hfinal.trans hf)))
    _ ≤ 100 * S ^ 100 := by omega
