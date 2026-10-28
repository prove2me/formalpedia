-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleValueEnvelope.schedule_value_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:50:08.833725+00:00
-- url     : https://prove2.me/submissions/4b6a1826-2afd-4a70-bbbc-e8fd95d54869

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

namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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

namespace CountingMatroid.Analysis.ScheduleDrawTrialsBridge

open CountingMatroid.Model
open CountingMatroid.Model.Operations

/-- INTERNAL: A search counter increases by at most one per successful iteration. -/
private theorem firstCounter_foldlWhile_le {α β : Type}
    (f : (ℕ × β) → α → Arlib.Computation.Charged Op Cell (Option (ℕ × β)))
    (hstep : ∀ b a b', (f b a).val = some b' → b'.1 ≤ b.1 + 1)
    (l : List α) (b : ℕ × β) :
    (Arlib.Computation.Charged.foldlWhile f l b).val.1 ≤ b.1 + l.length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    cases h : (f b a).val with
    | none =>
      simp only [Arlib.Computation.Charged.val] at h
      simp [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val, h]
    | some b' =>
      have hs := hstep b a b' h
      have hr := ih b'
      simp only [Arlib.Computation.Charged.val] at h
      simp only [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val,
        h, List.length_cons] at *
      omega

/-- INTERNAL: The charged draw-trial search cannot exceed its loop cap.
TEXLINE: main.tex:1397-1421 -/
private theorem leastDrawTrials_val_le_cap (M : ℕ) :
    (CountingMatroid.Program.leastDrawTrials M).val ≤ M.log2 + 9 := by
  unfold CountingMatroid.Program.leastDrawTrials
  simp only [Arlib.Computation.Charged.val_bind,
    CountingMatroid.Model.Operations.binaryLoopBound,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure]
  unfold Arlib.Computation.Charged.repeatWhile
  convert firstCounter_foldlWhile_le (f := _) ?_ (List.range (M.log2 + 8))
    (1, 2) using 1 <;> simp
  case e'_4 => omega
  intro b a b' b'q h
  split at h
  · simp only [successor, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_map, Arlib.Computation.Charged.val_op,
      natMul] at h
    cases h
    omega
  · simp at h



/-- INTERNAL: A property of the continuation value holds after a charged bind. -/
private theorem val_bind_property {α β : Type}
    (c : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β)
    (P : β → Prop) (h : ∀ x, P (f x).val) : P (c >>= f).val := by
  simpa only [Arlib.Computation.Charged.val_bind] using h c.val

/-- INTERNAL: The final schedule steps store the capped trial count.
TEXLINE: main.tex:1397-1421 -/
private theorem schedule_tail_good (bε : ℕ) (rho : ℚ) (L : ℕ) (eta : ℚ)
    (tau restartCap observations : ℕ) (p : InputParams) :
    drawCapGood (do
      let attemptsAndObservations ← natAdd restartCap observations
      let threeL ← natMul 3 L
      let drawCalls ← natMul threeL attemptsAndObservations
      let drawTrials ← CountingMatroid.Program.leastDrawTrials drawCalls
      let bδ ← CountingMatroid.Program.leastHalvings p.δ
      let tenBδ ← natMul 10 bδ
      let repetitions ← successor tenBδ
      pure (AnnealingSchedule.mk bε rho L eta tau restartCap observations
        drawCalls drawTrials bδ repetitions) :
        Arlib.Computation.Charged Op Cell AnnealingSchedule).val := by
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    natAdd, natMul, Arlib.Computation.Charged.val_op, drawCapGood]
  exact leastDrawTrials_val_le_cap _

/-- INTERNAL: The schedule's trial count is controlled by its charged draw-call count.
TEXLINE: main.tex:1397-1421 -/
theorem schedule_drawTrials_le_drawCalls (n : ℕ) (p : InputParams) :
    let s := (CountingMatroid.Program.schedule n p).val
    s.drawTrials ≤ (3 * s.L * (s.restartCap + s.observations)).log2 + 9 := by
  change drawCapGood (CountingMatroid.Program.schedule n p).val
  unfold CountingMatroid.Program.schedule
  iterate 29
    apply val_bind_property
    intro
  exact schedule_tail_good _ _ _ _ _ _ _ p

end CountingMatroid.Analysis.ScheduleDrawTrialsBridge

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · peeled the schedule's charged binds and bounded the final trial counter by its loop cap; full schedule reduction stalled.
-/

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

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleValueEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: A bounded charged search whose first state component rises by at
most one per successful round cannot exceed its round cap. -/
private theorem firstCounter_foldlWhile_le {α β : Type}
    (f : (ℕ × β) → α → Arlib.Computation.Charged Op Cell (Option (ℕ × β)))
    (hstep : ∀ b a b', (f b a).val = some b' → b'.1 ≤ b.1 + 1)
    (l : List α) (b : ℕ × β) :
    (Arlib.Computation.Charged.foldlWhile f l b).val.1 ≤ b.1 + l.length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    cases h : (f b a).val with
    | none =>
      simp only [Arlib.Computation.Charged.val] at h
      simp [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val, h]
    | some b' =>
      have hs := hstep b a b' h
      have hr := ih b'
      simp only [Arlib.Computation.Charged.val] at h
      simp only [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val,
        h, List.length_cons] at *
      omega

/-- INTERNAL: The halving search is bounded by its encoded denominator cap.
TEXLINE: main.tex:1348-1351 -/
private theorem leastHalvings_val_le_den (q : ℚ) :
    (CountingMatroid.Program.leastHalvings q).val ≤ q.den.log2 + 8 := by
  unfold CountingMatroid.Program.leastHalvings
  simp only [Arlib.Computation.Charged.val_bind,
    CountingMatroid.Model.Operations.binaryLoopBound,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure]
  unfold Arlib.Computation.Charged.repeatWhile
  convert firstCounter_foldlWhile_le (f := _) ?_ (List.range (q.den.log2 + 8))
    (0, (1 : ℚ)) using 1 <;> simp
  intro b a b' b'q h
  split at h
  · simp only [successor, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_map,
      Arlib.Computation.Charged.val_op, ratDiv,
      Arlib.Computation.Charged.val_opMany] at h
    cases h
    omega
  · simp at h

/-- INTERNAL: Dividing a rational by ten increases its denominator's binary
length by at most four.
TEXLINE: main.tex:1348-1351 -/
private theorem rat_div_ten_den_log2_le (q : ℚ) :
    (q / 10).den.log2 ≤ q.den.log2 + 4 := by
  have hdvd : (q / 10).den ∣ q.den * 10 := by
    convert Rat.mul_den_dvd q (1 / 10 : ℚ) using 1 <;> norm_num [div_eq_mul_inv]
  have hden : (q / 10).den ≤ q.den * 10 :=
    Nat.le_of_dvd (by positivity) hdvd
  have h16 : q.den * 10 ≤ q.den * 16 := by omega
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  calc
    Nat.log 2 (q / 10).den ≤ Nat.log 2 (q.den * 16) :=
      Nat.log_mono_right (le_trans hden h16)
    _ = Nat.log 2 q.den + 4 := by
      have hq : q.den ≠ 0 := q.den_nz
      have hqpos : 0 < q.den := q.den_pos
      conv_lhs => rw [show (16 : ℕ) = 2 * 2 * 2 * 2 by decide]
      simp only [← mul_assoc]
      rw [Nat.log_mul_base (by decide : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by decide : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by decide : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by decide : 1 < 2) hq]



/-- INTERNAL: The repetition count is ten times the confidence halving count,
plus one.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_repetitions_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.repetitions =
      10 * (CountingMatroid.Program.leastHalvings p.δ).val + 1 := by
  unfold CountingMatroid.Program.schedule
  simp only [Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, natMul, successor,
    Arlib.Computation.Charged.val_op]

/-- INTERNAL: The schedule's repetition count is linear in the input encoding.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_repetitions_le_input (n r : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.repetitions ≤
      10 * binaryInputLength n r p + 81 := by
  rw [schedule_repetitions_eq]
  have h := leastHalvings_val_le_den p.δ
  unfold binaryInputLength binaryRatLength binaryNatLength
  omega

/-- INTERNAL: The phase cap records the first halving search in the concrete
schedule formula.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_L_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.L =
      2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) := by
  unfold CountingMatroid.Program.schedule
  simp only [Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, natMul, natAdd, ratDiv,
    Arlib.Computation.Charged.val_op,
    Arlib.Computation.Charged.val_opMany]

/-- INTERNAL: The phase count is quadratic in the ground size and input
encoding length.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_L_le_input (n r : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.L ≤
      2 * n * (n + binaryInputLength n r p + 12) := by
  rw [schedule_L_eq]
  have hcap := leastHalvings_val_le_den (p.ε / 10)
  have hlog := rat_div_ten_den_log2_le p.ε
  have hbound :
      (CountingMatroid.Program.leastHalvings (p.ε / 10)).val ≤
        binaryInputLength n r p + 12 := by
    unfold binaryInputLength binaryRatLength binaryNatLength
    omega
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hbound n)

/-- INTERNAL: The trace length is the paper's explicit polynomial in the phase cap.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_tau_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.τ =
      20 * n ^ 4 *
        (n * (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) + 2) := by
  rfl

/-- INTERNAL: The restart cap is determined by the phase cap and trace length.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_restartCap_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.restartCap =
      2000 * ((CountingMatroid.Program.schedule n p).val.L + 1) ^ 2 * n ^ 2 *
        (CountingMatroid.Program.schedule n p).val.τ := by
  rfl

/-- INTERNAL: The observation count is the ceiling of the charged rational
quotient. TEXLINE: main.tex:1348-1355 -/
private theorem schedule_observations_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.observations =
      Nat.ceil (((10000000000 *
          (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) *
          n ^ 14 : ℕ) : ℚ) /
        (p.ε / (↑(32 *
          (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1)) : ℚ)) ^ 2) := by
  have hraw :
      (CountingMatroid.Program.schedule n p).val.observations =
        Int.toNat (((((10000000000 *
            (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) *
            (CountingMatroid.Program.natPower n 14).val : ℕ) : ℚ) /
          ((p.ε / (↑(32 *
            (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1)) : ℚ)) *
           (p.ε / (↑(32 *
            (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1)) : ℚ))))).ceil) := by
    rfl
  have hceil (q : ℚ) : q.ceil = ⌈q⌉ := by
    symm
    apply Int.ceil_eq_iff.mpr
    constructor
    · have h := Rat.ceil_lt (x := q)
      linarith
    · exact Rat.le_ceil
  rw [hceil, Int.ceil_toNat,
    CountingMatroid.Analysis.BoundedRunResourceEnvelope.natPower_value,
    ← pow_two] at hraw
  exact hraw

/-- INTERNAL: The observation count is bounded using the ceiling of inverse
accuracy, so the rational division cannot make it superpolynomial.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_observations_le (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.observations ≤
      10000000000 * ((CountingMatroid.Program.schedule n p).val.L + 1) * n ^ 14 *
        (32 * ((CountingMatroid.Program.schedule n p).val.L + 1)) ^ 2 *
        (Nat.ceil p.ε⁻¹) ^ 2 := by
  rw [schedule_observations_eq, schedule_L_eq]
  let A := 10000000000 *
    (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) * n ^ 14
  let B := 32 *
    (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1)
  change Nat.ceil ((A : ℚ) / (p.ε / (B : ℚ)) ^ 2) ≤
    A * B ^ 2 * (Nat.ceil p.ε⁻¹) ^ 2
  rw [Nat.ceil_le]
  have h : (A : ℚ) / (p.ε / (B : ℚ)) ^ 2 =
      (A : ℚ) * (B : ℚ) ^ 2 * p.ε⁻¹ ^ 2 := by
    field_simp
  rw [h]
  push_cast
  gcongr
  · exact (inv_pos.mpr p.ε_pos).le
  · exact Nat.le_ceil _

/-- INTERNAL: A rational in the unit interval has an encoding controlled by
its denominator. TEXLINE: main.tex:1348-1356 -/
private theorem binaryRatLength_le_den_of_unit (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : binaryRatLength q ≤ 2 * q.den + 4 := by
  have hn0 : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have hn1 : q.num ≤ (q.den : ℤ) := by
    have h := hq1
    rw [← q.num_div_den] at h
    have h' : (q.num : ℚ) ≤ (q.den : ℚ) := by
      simpa using (div_le_iff₀ (by exact_mod_cast q.den_pos)).mp h
    exact_mod_cast h'
  have hn : q.num.natAbs ≤ q.den := by
    have hn' : (q.num.natAbs : ℤ) ≤ (q.den : ℤ) := by
      simpa [Int.natAbs_of_nonneg hn0] using hn1
    exact_mod_cast hn'
  unfold binaryRatLength binaryNatLength
  have hlogn := Nat.log_le_self 2 q.num.natAbs
  have hlogd := Nat.log_le_self 2 q.den
  simp only [Nat.log2_eq_log_two]
  omega

/-- INTERNAL: The annealing ratio has denominator at most twice the ground size.
TEXLINE: main.tex:1348-1356 -/
private theorem schedule_rho_length_le (n : ℕ) (p : InputParams) :
    binaryRatLength (CountingMatroid.Program.schedule n p).val.ρ ≤ 4 * n + 6 := by
  have hρ : (CountingMatroid.Program.schedule n p).val.ρ =
      1 - 1 / (2 * n : ℚ) := by
    unfold CountingMatroid.Program.schedule
    simp only [Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, natMul, ratOfNat, ratDiv, ratSub,
      Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany]
    norm_num [Nat.cast_mul]
  rw [hρ]
  by_cases hn : n = 0
  · subst n
    simp [binaryRatLength, binaryNatLength, Nat.log2_eq_log_two]
  · have hnp : 0 < n := Nat.pos_of_ne_zero hn
    have hden : (1 - 1 / (2 * n : ℚ)).den = 2 * n := by
      have hcast : (2 * n : ℚ) = ((2 * n : ℕ) : ℚ) := by norm_num [Nat.cast_mul]
      rw [hcast, one_div, show (1 : ℚ) = ((1 : ℕ) : ℚ) by norm_num,
        Rat.natCast_sub_den, Rat.inv_natCast_den_of_pos (by omega : 0 < 2 * n)]
    have hunit0 : 0 ≤ (1 - 1 / (2 * n : ℚ)) := by
      have : (1 : ℚ) ≤ 2 * n := by exact_mod_cast (by omega : 1 ≤ 2 * n)
      have : 1 / (2 * n : ℚ) ≤ 1 := (div_le_iff₀ (by positivity)).2 (by nlinarith)
      linarith
    have hunit1 : (1 - 1 / (2 * n : ℚ)) ≤ 1 := by
      have : 0 ≤ 1 / (2 * n : ℚ) := by positivity
      linarith
    have hb := binaryRatLength_le_den_of_unit _ hunit0 hunit1
    rw [hden] at hb
    omega






end CountingMatroid.Analysis.ScheduleValueEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r11 · closed · bounded the trace, restart cap, observations, draw trials, and remaining fields by powers of encoded input size.
* r10 · partial · proved rho and L bounds, including n=0; separated the draw-trial bridge and encountered heartbeat limits combining the explicit tau formula.
* r9 · partial · proved tau and restart formulas and a polynomial observation ceiling bound; the rho encoding and common envelope remain open.
* r8 · open · proved search caps, denominator growth under division by ten, and L and repetition bounds; full value envelope still needs observation quotient and later-field bounds.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleValueEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The concrete schedule fields have a common polynomial envelope
in the encoded input size.
TEXLINE: main.tex:1348-1356, 1397-1421 -/
theorem solution :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let s := (CountingMatroid.Program.schedule n p).val
      n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
        binaryRatLength s.ρ + s.repetitions + 1 ≤ C * inputSize ^ degree := by
  refine ⟨10 ^ 500, 50, ?_⟩
  intro n r p
  let s := (CountingMatroid.Program.schedule n p).val
  let X := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹) + 1
  have hdraw := ScheduleDrawTrialsBridge.schedule_drawTrials_le_drawCalls n p
  have hrho := schedule_rho_length_le n p
  change s.drawTrials ≤ (3 * s.L * (s.restartCap + s.observations)).log2 + 9 at hdraw
  change binaryRatLength s.ρ ≤ 4 * n + 6 at hrho
  let Y := 10000000000 * X
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hnX : n ≤ X := by dsimp [X]; omega
  have hbinX : binaryInputLength n r p ≤ X := by dsimp [X]; omega
  have hεX : Nat.ceil p.ε⁻¹ ≤ X := by dsimp [X]; omega
  have hY : 10000000000 ≤ Y := by dsimp [Y]; nlinarith
  have hnY : n ≤ Y := by dsimp [Y]; omega
  have hεY : Nat.ceil p.ε⁻¹ ≤ Y := by dsimp [Y]; omega
  have hLY : s.L ≤ Y ^ 2 := by
    have hL := schedule_L_le_input n r p
    change s.L ≤ 2 * n * (n + binaryInputLength n r p + 12) at hL
    calc
      s.L ≤ 2 * n * (n + binaryInputLength n r p + 12) := hL
      _ ≤ 2 * X * (14 * X) := by gcongr <;> omega
      _ = 28 * X ^ 2 := by ring
      _ ≤ Y ^ 2 := by
        calc
          28 * X ^ 2 ≤ 10000000000 ^ 2 * X ^ 2 := by gcongr; norm_num
          _ = Y ^ 2 := by dsimp [Y]; ring
  have hY1 : 1 ≤ Y := by omega
  have hY2 : 2 ≤ Y := by omega
  have hLp : s.L + 1 ≤ Y ^ 3 := by
    have hpow : 1 ≤ Y ^ 2 := one_le_pow₀ hY1
    calc
      s.L + 1 ≤ Y ^ 2 + 1 := by omega
      _ ≤ 2 * Y ^ 2 := by omega
      _ ≤ Y * Y ^ 2 := Nat.mul_le_mul_right _ hY2
      _ = Y ^ 3 := by ring
  have hinner : n * (s.L + 1) + 2 ≤ Y ^ 5 := by
    have hY4 : 2 ≤ Y ^ 4 := by
      exact hY2.trans (le_self_pow hY1 (by decide))
    calc
      n * (s.L + 1) + 2 ≤ Y * Y ^ 3 + 2 := by gcongr
      _ = Y ^ 4 + 2 := by ring
      _ ≤ 2 * Y ^ 4 := by omega
      _ ≤ Y * Y ^ 4 := Nat.mul_le_mul_right _ hY2
      _ = Y ^ 5 := by ring
  have hτ : s.τ ≤ Y ^ 10 := by
    have hb : (CountingMatroid.Program.leastHalvings (p.ε / 10)).val ≤
        binaryInputLength n r p + 12 := by
      have hcap := leastHalvings_val_le_den (p.ε / 10)
      have hlog := rat_div_ten_den_log2_le p.ε
      unfold binaryInputLength binaryRatLength binaryNatLength
      omega
    have hin : n * (2 * n * (n +
        (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) + 2 ≤
        Y ^ 5 := by
      have hpart : 2 * n * (n +
          (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) ≤ Y ^ 2 := by
        calc
          _ ≤ 2 * X * (14 * X) := by gcongr <;> omega
          _ = 28 * X ^ 2 := by ring
          _ ≤ Y ^ 2 := by
            calc
              28 * X ^ 2 ≤ 10000000000 ^ 2 * X ^ 2 := by gcongr; norm_num
              _ = Y ^ 2 := by dsimp [Y]; ring
      have hp : 2 * n * (n +
          (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1 ≤ Y ^ 3 := by
        have : 1 ≤ Y ^ 2 := one_le_pow₀ hY1
        calc
          _ ≤ Y ^ 2 + 1 := by omega
          _ ≤ 2 * Y ^ 2 := by omega
          _ ≤ Y * Y ^ 2 := Nat.mul_le_mul_right _ hY2
          _ = Y ^ 3 := by
            calc
              Y * Y ^ 2 = Y ^ 2 * Y := by ac_rfl
              _ = Y ^ 3 := (pow_succ Y 2).symm
      calc
        _ ≤ Y * Y ^ 3 + 2 := by gcongr
        _ = Y ^ 4 + 2 := by
          exact congrArg (fun t : ℕ => t + 2)
            ((mul_comm Y (Y ^ 3)).trans (pow_succ Y 3).symm)
        _ ≤ 2 * Y ^ 4 := by
          have : 2 ≤ Y ^ 4 := hY2.trans (le_self_pow hY1 (by decide))
          omega
        _ ≤ Y * Y ^ 4 := Nat.mul_le_mul_right _ hY2
        _ = Y ^ 5 := by
          calc
            Y * Y ^ 4 = Y ^ 4 * Y := by ac_rfl
            _ = Y ^ 5 := (pow_succ Y 4).symm
    calc
      s.τ = 20 * n ^ 4 * (n * (2 * n * (n +
          (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) + 2) :=
        schedule_tau_eq n p
      _ ≤ 20 * Y ^ 4 * Y ^ 5 := by gcongr
      _ = 20 * Y ^ 9 := by
        calc
          20 * Y ^ 4 * Y ^ 5 = 20 * (Y ^ 4 * Y ^ 5) := by ac_rfl
          _ = 20 * Y ^ (4 + 5) := by rw [pow_add]
          _ = 20 * Y ^ 9 := by norm_num
      _ ≤ Y * Y ^ 9 := Nat.mul_le_mul_right _ (by omega)
      _ = Y ^ 10 := by
        calc
          Y * Y ^ 9 = Y ^ 9 * Y := by ac_rfl
          _ = Y ^ 10 := (pow_succ Y 9).symm
  have hR : s.restartCap ≤ Y ^ 19 := by
    have hpoly (z : ℕ) : 2000 * (z ^ 3) ^ 2 * z ^ 2 * z ^ 10 =
        2000 * z ^ 18 := by ring
    calc
      s.restartCap = 2000 * (s.L + 1) ^ 2 * n ^ 2 * s.τ :=
        schedule_restartCap_eq n p
      _ ≤ 2000 * (Y ^ 3) ^ 2 * Y ^ 2 * Y ^ 10 := by gcongr
      _ = 2000 * Y ^ 18 := hpoly Y
      _ ≤ Y * Y ^ 18 := Nat.mul_le_mul_right _ (by omega)
      _ = Y ^ 19 := by
        calc
          Y * Y ^ 18 = Y ^ 18 * Y := mul_comm _ _
          _ = Y ^ 19 := (pow_succ Y 18).symm
  have hO : s.observations ≤ Y ^ 27 := by
    have hraw := schedule_observations_le n p
    change s.observations ≤ 10000000000 * (s.L + 1) * n ^ 14 *
      (32 * (s.L + 1)) ^ 2 * (Nat.ceil p.ε⁻¹) ^ 2 at hraw
    have hpoly (z : ℕ) : 10000000000 * z ^ 3 * z ^ 14 *
        (32 * z ^ 3) ^ 2 * z ^ 2 = 10240000000000 * z ^ 25 := by ring
    have hconst : 10240000000000 ≤ Y ^ 2 := by
      calc
        10240000000000 ≤ 10000000000 ^ 2 := by norm_num
        _ ≤ Y ^ 2 := by gcongr
    have hmono (a b c A B C : ℕ) (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
        10000000000 * a * b ^ 14 * (32 * a) ^ 2 * c ^ 2 ≤
          10000000000 * A * B ^ 14 * (32 * A) ^ 2 * C ^ 2 := by
      have hpowB : b ^ 14 ≤ B ^ 14 := pow_le_pow_left₀ (Nat.zero_le _) hb _
      have hpowA : (32 * a) ^ 2 ≤ (32 * A) ^ 2 :=
        pow_le_pow_left₀ (Nat.zero_le _) (Nat.mul_le_mul_left 32 ha) _
      have hpowC : c ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (Nat.zero_le _) hc _
      have hKa : 10000000000 * a ≤ 10000000000 * A :=
        Nat.mul_le_mul_left _ ha
      have hKab : 10000000000 * a * b ^ 14 ≤
          10000000000 * A * B ^ 14 := by
        calc
          _ ≤ 10000000000 * A * b ^ 14 := Nat.mul_le_mul_right _ hKa
          _ ≤ 10000000000 * A * B ^ 14 := Nat.mul_le_mul_left _ hpowB
      have hKabA : 10000000000 * a * b ^ 14 * (32 * a) ^ 2 ≤
          10000000000 * A * B ^ 14 * (32 * A) ^ 2 := by
        calc
          _ ≤ 10000000000 * A * B ^ 14 * (32 * a) ^ 2 :=
            Nat.mul_le_mul_right _ hKab
          _ ≤ 10000000000 * A * B ^ 14 * (32 * A) ^ 2 :=
            Nat.mul_le_mul_left _ hpowA
      calc
        _ ≤ 10000000000 * A * B ^ 14 * (32 * A) ^ 2 * c ^ 2 :=
          Nat.mul_le_mul_right _ hKabA
        _ ≤ 10000000000 * A * B ^ 14 * (32 * A) ^ 2 * C ^ 2 :=
          Nat.mul_le_mul_left _ hpowC
    calc
      s.observations ≤ 10000000000 * (s.L + 1) * n ^ 14 *
          (32 * (s.L + 1)) ^ 2 * (Nat.ceil p.ε⁻¹) ^ 2 := hraw
      _ ≤ 10000000000 * Y ^ 3 * Y ^ 14 *
          (32 * Y ^ 3) ^ 2 * Y ^ 2 := hmono _ _ _ _ _ _ hLp hnY hεY
      _ = 10240000000000 * Y ^ 25 := hpoly Y
      _ ≤ Y ^ 2 * Y ^ 25 := Nat.mul_le_mul_right _ hconst
      _ = Y ^ 27 := (pow_add Y 2 25).symm
  have hD : s.drawTrials ≤ Y ^ 31 := by
    let m := 3 * s.L * (s.restartCap + s.observations)
    have hlog : m.log2 ≤ m := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 m
    have hR27 : s.restartCap ≤ Y ^ 27 :=
      hR.trans (pow_le_pow_right₀ hY1 (by decide : 19 ≤ 27))
    have hsum : s.restartCap + s.observations ≤ 2 * Y ^ 27 := by omega
    have hprod : m ≤ 3 * Y ^ 2 * (2 * Y ^ 27) := by
      dsimp [m]
      calc
        _ ≤ 3 * Y ^ 2 * (s.restartCap + s.observations) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hLY)
        _ ≤ 3 * Y ^ 2 * (2 * Y ^ 27) :=
          Nat.mul_le_mul_left _ hsum
    have hpoly (z : ℕ) : 3 * z ^ 2 * (2 * z ^ 27) = 6 * z ^ 29 := by ring
    have hY29 : 9 ≤ Y ^ 29 := by
      have hpow : Y ≤ Y ^ 29 := le_self_pow hY1 (by decide)
      omega
    have hcoef : 15 ≤ Y ^ 2 := by
      have hpow : Y ≤ Y ^ 2 := le_self_pow hY1 (by decide)
      omega
    calc
      s.drawTrials ≤ m.log2 + 9 := hdraw
      _ ≤ m + 9 := by omega
      _ ≤ 3 * Y ^ 2 * (2 * Y ^ 27) + 9 := by omega
      _ = 6 * Y ^ 29 + 9 := by rw [hpoly]
      _ ≤ 15 * Y ^ 29 := by omega
      _ ≤ Y ^ 2 * Y ^ 29 := Nat.mul_le_mul_right _ hcoef
      _ = Y ^ 31 := (pow_add Y 2 29).symm
  change n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
    binaryRatLength s.ρ + s.repetitions + 1 ≤ 10 ^ 500 * X ^ 50
  have hrep := schedule_repetitions_le_input n r p
  change s.repetitions ≤ 10 * binaryInputLength n r p + 81 at hrep
  have hbinY : binaryInputLength n r p ≤ Y := by dsimp [Y]; omega
  have hYsq : 91 * Y ≤ Y ^ 2 := by
    have h91 : 91 ≤ Y := by omega
    calc
      91 * Y ≤ Y * Y := Nat.mul_le_mul_right _ h91
      _ = Y ^ 2 := (pow_two Y).symm
  have hrep31 : s.repetitions ≤ Y ^ 31 := by
    calc
      s.repetitions ≤ 10 * binaryInputLength n r p + 81 := hrep
      _ ≤ 91 * Y := by omega
      _ ≤ Y ^ 2 := hYsq
      _ ≤ Y ^ 31 := pow_le_pow_right₀ hY1 (by decide)
  have hrho31 : binaryRatLength s.ρ ≤ Y ^ 31 := by
    calc
      binaryRatLength s.ρ ≤ 4 * n + 6 := hrho
      _ ≤ 91 * Y := by omega
      _ ≤ Y ^ 2 := hYsq
      _ ≤ Y ^ 31 := pow_le_pow_right₀ hY1 (by decide)
  have hn31 : n ≤ Y ^ 31 := hnY.trans (le_self_pow hY1 (by decide))
  have hL31 : s.L ≤ Y ^ 31 := hLY.trans (pow_le_pow_right₀ hY1 (by decide))
  have hτ31 : s.τ ≤ Y ^ 31 := hτ.trans (pow_le_pow_right₀ hY1 (by decide))
  have hR31 : s.restartCap ≤ Y ^ 31 := hR.trans (pow_le_pow_right₀ hY1 (by decide))
  have hO31 : s.observations ≤ Y ^ 31 := hO.trans (pow_le_pow_right₀ hY1 (by decide))
  have h1 : 1 ≤ Y ^ 31 := one_le_pow₀ hY1
  have htotal : n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
      binaryRatLength s.ρ + s.repetitions + 1 ≤ 9 * Y ^ 31 := by omega
  have hYpow : Y ^ 31 = 10000000000 ^ 31 * X ^ 31 := by
    change (10000000000 * X) ^ 31 = 10000000000 ^ 31 * X ^ 31
    exact mul_pow _ _ _
  have hconstFinal : 9 * 10000000000 ^ 31 ≤ 10 ^ 500 := by
    calc
      9 * 10000000000 ^ 31 ≤ 10 * 10000000000 ^ 31 :=
        Nat.mul_le_mul_right _ (by decide)
      _ = 10 ^ 311 := by
        rw [show (10000000000 : ℕ) = 10 ^ 10 by norm_num, ← pow_mul]
        change 10 * 10 ^ 310 = 10 ^ 311
        calc
          10 * 10 ^ 310 = 10 ^ 310 * 10 := mul_comm _ _
          _ = 10 ^ 311 := (pow_succ 10 310).symm
      _ ≤ 10 ^ 500 := pow_le_pow_right₀ (by decide) (by decide)
  calc
    _ ≤ 9 * Y ^ 31 := htotal
    _ = (9 * 10000000000 ^ 31) * X ^ 31 := by rw [hYpow, mul_assoc]
    _ ≤ 10 ^ 500 * X ^ 31 :=
      Nat.mul_le_mul_right _ hconstFinal
    _ ≤ 10 ^ 500 * X ^ 50 :=
      Nat.mul_le_mul_left _ (pow_le_pow_right₀ hX (by decide))
