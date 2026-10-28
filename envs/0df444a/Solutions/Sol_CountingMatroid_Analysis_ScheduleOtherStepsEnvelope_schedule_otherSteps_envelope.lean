-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.schedule_otherSteps_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:14:23.470915+00:00
-- url     : https://prove2.me/submissions/37fef39a-6cc8-4c9f-a218-85421c1be57e

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
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
import Theorems.Thm_CountingMatroid_Analysis_LeastHalvingsCost_leastHalvings_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_binaryRatLength_mul_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_leastHalvings_value_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_rationalCeil_value_le_num
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_scheduleOpening_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_thermalRest_otherSteps_poly
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_thermalSetup_otherSteps_le

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
section

set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope



/-- INTERNAL: The source schedule is exactly its opening followed by its remainder.
TEXLINE: main.tex:1348-1358 -/
theorem schedule_split (n : ℕ) (p : InputParams) :
    CountingMatroid.Program.schedule n p = scheduleOpening n p >>= scheduleRemaining n p := by
  simp only [CountingMatroid.Program.schedule, scheduleOpening, scheduleRemaining, bind_assoc, pure_bind]
/-- INTERNAL: The opening computation produces the values used by the
remaining schedule operations. -/
theorem scheduleOpening_value (n : ℕ) (p : InputParams) :
    (scheduleOpening n p).val =
      ⟨(CountingMatroid.Program.leastHalvings (p.ε / 10)).val,
        1 - 1 / (2 * n : ℚ), 2 * n⟩ := by
  simp [scheduleOpening, ratDiv, ratSub, natMul, ratOfNat]







end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end

section

set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope



/-- INTERNAL: The opening remainder splits exactly at the thermal setup.
TEXLINE: main.tex:1348-1358 -/
theorem scheduleRemaining_split (n : ℕ) (p : InputParams) (head : ScheduleOpeningResult) :
    scheduleRemaining n p head = thermalSetup n p head >>= thermalRest n p := by
  simp only [scheduleRemaining, thermalSetup, thermalRest, bind_assoc, pure_bind]






/-- INTERNAL: Thermal setup returns the phase count, its successor,
the accuracy denominator, and the resulting accuracy. -/
theorem thermalSetup_value (n : ℕ) (p : InputParams)
    (head : ScheduleOpeningResult) :
    let L := head.twoN * (n + head.bε)
    let D := 32 * (L + 1)
    (thermalSetup n p head).val =
      ⟨head, L, L + 1, D, p.ε / (D : ℚ)⟩ := by
  dsimp only
  simp [thermalSetup, natAdd, natMul, successor, ratOfNat, ratDiv]






end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines















/-- INTERNAL: Rational inversion swaps numerator and denominator lengths. -/
theorem binaryRatLength_inv_eq (q : ℚ) :
    binaryRatLength q⁻¹ = binaryRatLength q := by
  by_cases hz : q.num = 0
  · have hq : q = 0 := Rat.zero_of_num_zero hz
    simp [hq]
  · unfold binaryRatLength binaryNatLength
    simp [Rat.num_inv, Rat.den_inv, Int.natAbs_mul,
      Int.natAbs_sign, hz, Int.natAbs_natCast]
    omega

/-- INTERNAL: Rational division adds no more binary encoding length than
multiplication by the denominator's reciprocal. -/
theorem binaryRatLength_div_le (q s : ℚ) :
    binaryRatLength (q / s) ≤ binaryRatLength q + binaryRatLength s := by
  rw [div_eq_mul_inv]
  simpa only [binaryRatLength_inv_eq] using binaryRatLength_mul_le q s⁻¹





/-- INTERNAL: A natural cast needs its own binary length plus three framing bits. -/
theorem binaryRatLength_natCast (a : ℕ) :
    binaryRatLength (a : ℚ) = a.log2 + 4 := by
  simp only [binaryRatLength, binaryNatLength, Rat.num_natCast,
    Rat.den_natCast, Int.natAbs_natCast]
  have h : (1 : ℕ).log2 = 0 := by decide
  rw [h]
  omega

/-- INTERNAL: A rational ceiling's binary logarithm fits within the rational
operand's encoding length. -/
theorem rationalCeil_log2_le (q : ℚ) :
    ((CountingMatroid.Model.Operations.rationalCeil q).val).log2 ≤
      binaryRatLength q := by
  have h := Nat.log_mono_right (b := 2) (rationalCeil_value_le_num q)
  rw [← Nat.log2_eq_log_two, ← Nat.log2_eq_log_two] at h
  unfold binaryRatLength binaryNatLength
  omega

/-- INTERNAL: The schedule's observation quotient has encoding length
controlled by the numerator and the encoded accuracy and denominator.
TEXLINE: main.tex:1348-1360 -/
theorem observationQuotient_length_le (a b : ℕ) (q : ℚ) :
    binaryRatLength ((a : ℚ) / ((q / (b : ℚ)) * (q / (b : ℚ)))) ≤
      a.log2 + 2 * binaryRatLength q + 2 * b.log2 + 12 := by
  have hdiv := binaryRatLength_div_le q (b : ℚ)
  have hmul := binaryRatLength_mul_le (q / (b : ℚ)) (q / (b : ℚ))
  have hquot := binaryRatLength_div_le (a : ℚ)
    ((q / (b : ℚ)) * (q / (b : ℚ)))
  rw [binaryRatLength_natCast] at hdiv hquot
  omega





end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Analysis.ResourceBound (otherSteps_bind)

/-- INTERNAL: A fixed polynomial absorbs the six opening-charge bounds. -/
private theorem openingPolynomial_arith (S : ℕ) (hS : 1 ≤ S) :
    (S + 7) ^ 2 + (100 * (S + 15) * (2 * S + 30) ^ 2 + 1) +
      1 + (2 * S + 1) + (2 * S + 8) ^ 2 + (2 * S + 12) ^ 2 ≤
      2000000 * S ^ 4 := by
  have h1 : S ≤ S ^ 4 := by simpa only [pow_one] using
    (pow_le_pow_right₀ hS (by decide : 1 ≤ 4))
  have h2 : S ^ 2 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide)
  have h4 : 1 ≤ S ^ 4 := by
    simpa only [pow_zero] using (pow_le_pow_right₀ hS (by decide : 0 ≤ 4))
  calc
    _ = 400 * S ^ 3 + 18009 * S ^ 2 + 270096 * S + 1350260 := by ring
    _ ≤ 2000000 * S ^ 4 := by omega

/-- INTERNAL: The thermal setup's rational division fits a quartic size bound. -/
private theorem thermalPolynomial_arith (S : ℕ) (hS : 1 ≤ S) :
    5 + 1120 * S ^ 2 + (S + 1120 * S ^ 2 + 4) ^ 2 ≤
      2000000 * S ^ 4 := by
  have h1 : S ≤ S ^ 2 := by simpa only [pow_one] using
    (pow_le_pow_right₀ hS (by decide : 1 ≤ 2))
  have h2 : S ^ 2 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide)
  have h4 : 1 ≤ S ^ 4 := by
    simpa only [pow_zero] using (pow_le_pow_right₀ hS (by decide : 0 ≤ 4))
  have hinner : S + 1120 * S ^ 2 + 4 ≤ 1125 * S ^ 2 := by omega
  have hsq := Nat.pow_le_pow_left hinner 2
  calc
    _ ≤ 5 + 1120 * S ^ 2 + (1125 * S ^ 2) ^ 2 := by omega
    _ = 5 + 1120 * S ^ 2 + 1265625 * S ^ 4 := by ring
    _ ≤ 2000000 * S ^ 4 := by omega



end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r14b · pending · the parent elaborates through the isolated tail lemma;
  the live handoff request was refused before capture.
* r14 · recovery · split the schedule into opening, thermal setup, and tail;
  proved the first two cost bounds and handed off the isolated tail bound.
* r13 · partial · proved the observation-quotient length and its ceiling-log
  polynomial bound and input-size bounds for both halving searches;
  schedule-cost normalization remains open.
* r12 · partial · proved capped-loop, rational-length, and ceiling-logarithm
  helpers; the full schedule sum still needs intermediate-value bookkeeping.
* r11 · partial · proved charged sequencing and natural-power costs; isolated the
  halving-loop cost and imported its checked child statement. The full schedule
  cost still needs rational operand-size bounds and a sum of all primitive costs.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Analysis.ResourceBound (otherSteps_bind)

/-- INTERNAL: The nonoracle charges of the concrete schedule have a common
polynomial bound in the encoded input size.
TEXLINE: main.tex:1348-1358 -/
theorem solution :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      otherSteps (CountingMatroid.Program.schedule n p) ≤
        C * inputSize ^ degree := by
  refine ⟨10 ^ 500, 50, ?_⟩
  intro n r p
  have hε := LeastHalvingsCost.leastHalvings_otherSteps_le (p.ε / 10)
  have hδ := LeastHalvingsCost.leastHalvings_otherSteps_le p.δ
  have hbε := leastHalvings_value_le (p.ε / 10)
  have hbδ := leastHalvings_value_le p.δ
  have hεlength : binaryRatLength (p.ε / 10) ≤ binaryRatLength p.ε + 7 := by
    have hten : binaryRatLength (10 : ℚ) = 7 := by decide
    simpa only [hten] using binaryRatLength_div_le p.ε 10
  let S := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹) + 1
  have hSpos : 0 < S := by dsimp [S]; omega
  have hnS : n ≤ S := by dsimp [S]; omega
  have hεS : binaryRatLength p.ε ≤ S := by
    dsimp [S, binaryInputLength]
    omega
  have hδS : binaryRatLength p.δ ≤ S := by
    dsimp [S, binaryInputLength]
    omega
  have hεlengthS : binaryRatLength (p.ε / 10) ≤ S + 7 := by omega
  have hεden : (p.ε / 10).den.log2 ≤ S + 7 := by
    unfold binaryRatLength binaryNatLength at hεlengthS
    omega
  have hδden : p.δ.den.log2 ≤ S := by
    unfold binaryRatLength binaryNatLength at hδS
    omega
  have hεcost : otherSteps (CountingMatroid.Program.leastHalvings (p.ε / 10)) ≤
      100 * (S + 15) * (2 * S + 30) ^ 2 + 1 := by
    calc
      _ ≤ 100 * ((p.ε / 10).den.log2 + 8) *
          (binaryRatLength (p.ε / 10) + (p.ε / 10).den.log2 + 16) ^ 2 + 1 := hε
      _ ≤ 100 * (S + 15) * (2 * S + 30) ^ 2 + 1 := by
        have h1 : 100 * ((p.ε / 10).den.log2 + 8) ≤ 100 * (S + 15) := by omega
        have h2 : (binaryRatLength (p.ε / 10) +
            (p.ε / 10).den.log2 + 16) ^ 2 ≤ (2 * S + 30) ^ 2 := by
          apply Nat.pow_le_pow_left
          omega
        exact Nat.add_le_add_right (Nat.mul_le_mul h1 h2) 1
  have hδcost : otherSteps (CountingMatroid.Program.leastHalvings p.δ) ≤
      100 * (S + 8) * (2 * S + 16) ^ 2 + 1 := by
    calc
      _ ≤ 100 * (p.δ.den.log2 + 8) *
          (binaryRatLength p.δ + p.δ.den.log2 + 16) ^ 2 + 1 := hδ
      _ ≤ 100 * (S + 8) * (2 * S + 16) ^ 2 + 1 := by
        have h1 : 100 * (p.δ.den.log2 + 8) ≤ 100 * (S + 8) := by omega
        have h2 : (binaryRatLength p.δ + p.δ.den.log2 + 16) ^ 2 ≤
            (2 * S + 16) ^ 2 := by
          apply Nat.pow_le_pow_left
          omega
        exact Nat.add_le_add_right (Nat.mul_le_mul h1 h2) 1
  let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
  let L := 2 * n * (n + b)
  let D := 32 * (L + 1)
  let A := 10000000000 * (L + 1) * n ^ 14
  have hbS : b ≤ S + 15 := by dsimp [b]; omega
  have hL : L ≤ 34 * S ^ 2 := by
    have hnb : n + b ≤ 17 * S := by omega
    calc
      L = 2 * n * (n + b) := rfl
      _ ≤ (2 * S) * (17 * S) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hnS) hnb
      _ = 34 * S ^ 2 := by ring
  have hD : D ≤ 1120 * S ^ 2 := by
    have hSsq : 1 ≤ S ^ 2 := by nlinarith
    dsimp [D]
    omega
  have hA : A ≤ 350000000000 * S ^ 16 := by
    have hSsq : 1 ≤ S ^ 2 := by nlinarith
    have hL1 : L + 1 ≤ 35 * S ^ 2 := by omega
    have hn14 : n ^ 14 ≤ S ^ 14 := Nat.pow_le_pow_left hnS 14
    calc
      A = 10000000000 * (L + 1) * n ^ 14 := rfl
      _ ≤ (10000000000 * (35 * S ^ 2)) * S ^ 14 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 10000000000 hL1) hn14
      _ = 350000000000 * S ^ 16 := by
        calc
          10000000000 * (35 * S ^ 2) * S ^ 14 =
              (10000000000 * 35) * (S ^ 2 * S ^ 14) := by ac_rfl
          _ = 350000000000 * S ^ 16 := by norm_num [← pow_add]
  have hDlog : D.log2 ≤ 1120 * S ^ 2 := by
    calc
      D.log2 ≤ D := by
        simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 D
      _ ≤ 1120 * S ^ 2 := hD
  have hAlog : A.log2 ≤ 350000000000 * S ^ 16 := by
    calc
      A.log2 ≤ A := by
        simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 A
      _ ≤ 350000000000 * S ^ 16 := hA
  have hObsLog :
      ((CountingMatroid.Model.Operations.rationalCeil
        ((A : ℚ) / ((p.ε / (D : ℚ)) * (p.ε / (D : ℚ))))).val).log2 ≤
        A.log2 + 2 * binaryRatLength p.ε + 2 * D.log2 + 12 := by
    exact (rationalCeil_log2_le _).trans
      (observationQuotient_length_le A D p.ε)
  have hObsLogPoly :
      ((CountingMatroid.Model.Operations.rationalCeil
        ((A : ℚ) / ((p.ε / (D : ℚ)) * (p.ε / (D : ℚ))))).val).log2 ≤
        350000000000 * S ^ 16 + 2 * S + 2240 * S ^ 2 + 12 := by
    omega
  rw [schedule_split n p, otherSteps_bind, scheduleOpening_value]
  have hopen := scheduleOpening_otherSteps_le n p
  have hTwoNLog : (2 * n).log2 ≤ 2 * S := by
    calc
      (2 * n).log2 ≤ 2 * n := by
        simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 (2 * n)
      _ ≤ 2 * S := by omega
  have hTwoNLength : binaryRatLength (2 * n : ℚ) ≤ 2 * S + 4 := by
    have h := binaryRatLength_natCast (2 * n)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    omega
  have hInvLength : binaryRatLength (1 / (2 * n : ℚ)) ≤ 2 * S + 8 := by
    have h := binaryRatLength_div_le (1 : ℚ) (2 * n : ℚ)
    have hOne : binaryRatLength (1 : ℚ) = 4 := by decide
    omega
  have hopenPoly : otherSteps (scheduleOpening n p) ≤ 2000000 * S ^ 4 := by
    have h1 : (binaryRatLength p.ε + 7) ^ 2 ≤ (S + 7) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega) 2
    have h2 : (4 + binaryRatLength (2 * n : ℚ)) ^ 2 ≤
        (2 * S + 8) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega) 2
    have h3 : (4 + binaryRatLength (1 / (2 * n : ℚ))) ^ 2 ≤
        (2 * S + 12) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega) 2
    have hbound : otherSteps (scheduleOpening n p) ≤
        (S + 7) ^ 2 + (100 * (S + 15) * (2 * S + 30) ^ 2 + 1) +
        1 + (2 * S + 1) + (2 * S + 8) ^ 2 + (2 * S + 12) ^ 2 := by
      omega
    exact hbound.trans (openingPolynomial_arith S (by omega))
  suffices hremaining :
      otherSteps (scheduleRemaining n p
        ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤ 10 ^ 200 * S ^ 45 by
    change otherSteps (scheduleOpening n p) +
      otherSteps (scheduleRemaining n p
        ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤ 10 ^ 500 * S ^ 50
    have h4 : S ^ 4 ≤ S ^ 50 := pow_le_pow_right₀ (by omega) (by decide)
    have h45 : S ^ 45 ≤ S ^ 50 := pow_le_pow_right₀ (by omega) (by decide)
    have h50 : 1 ≤ S ^ 50 := by
      simpa only [pow_zero] using (pow_le_pow_right₀ (by omega : 1 ≤ S)
        (by decide : 0 ≤ 50))
    have hcost : otherSteps (scheduleOpening n p) +
        otherSteps (scheduleRemaining n p
          ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤
        2000000 * S ^ 4 + 10 ^ 200 * S ^ 45 :=
      Nat.add_le_add hopenPoly hremaining
    omega
  rw [scheduleRemaining_split, otherSteps_bind, thermalSetup_value]
  change otherSteps (thermalSetup n p ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) +
    otherSteps (thermalRest n p
      ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, p.ε / (D : ℚ)⟩) ≤
      10 ^ 200 * S ^ 45
  have hthermal := thermalSetup_otherSteps_le n p
    (⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩ : ScheduleOpeningResult)
  change otherSteps (thermalSetup n p
    ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤
      5 + D.log2 + (binaryRatLength p.ε + binaryRatLength (D : ℚ)) ^ 2 at hthermal
  have hDLength : binaryRatLength (D : ℚ) ≤ 1120 * S ^ 2 + 4 := by
    rw [binaryRatLength_natCast]
    omega
  have hinner : binaryRatLength p.ε + binaryRatLength (D : ℚ) ≤
      S + 1120 * S ^ 2 + 4 := by omega
  have hthermalPoly : otherSteps (thermalSetup n p
      ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤ 2000000 * S ^ 4 := by
    have hsq := Nat.pow_le_pow_left hinner 2
    have hbound : otherSteps (thermalSetup n p
        ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤
        5 + 1120 * S ^ 2 + (S + 1120 * S ^ 2 + 4) ^ 2 := by omega
    exact hbound.trans (thermalPolynomial_arith S (by omega))
  suffices htail : otherSteps (thermalRest n p
      ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, p.ε / (D : ℚ)⟩) ≤
        10 ^ 150 * S ^ 40 by
    have h4 : S ^ 4 ≤ S ^ 45 := pow_le_pow_right₀ (by omega) (by decide)
    have h40 : S ^ 40 ≤ S ^ 45 := pow_le_pow_right₀ (by omega) (by decide)
    have h45 : 1 ≤ S ^ 45 := by
      simpa only [pow_zero] using (pow_le_pow_right₀ (by omega : 1 ≤ S)
        (by decide : 0 ≤ 45))
    have hcost := Nat.add_le_add hthermalPoly htail
    omega
  exact thermalRest_otherSteps_poly n r p
