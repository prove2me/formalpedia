-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalRest_otherSteps_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:08:04.666986+00:00
-- url     : https://prove2.me/submissions/79b6b85c-5bf8-4ebf-8a67-e27c025a8013

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
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_leastDrawTrials_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_leastHalvings_value_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_log2_add_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_log2_mul_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_natPower_otherSteps_eq
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_rationalCeil_value_le_num
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_thermalRest_cost_eq

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

/-- INTERNAL: A charged rational binary operation is bounded by its input encodings. -/
theorem rationalBinary_otherSteps_le (instr : Arlib.Computation.Op)
    (a b result : ℚ) :
    otherSteps (Arlib.Computation.Charged.opMany
      (CountingMatroid.Model.Operations.Op.word instr)
      ((a.num.natAbs.log2 + a.den.log2 + 3 +
        (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2) result) ≤
      (binaryRatLength a + binaryRatLength b) ^ 2 := by
  have hcost (z : ℕ) : otherSteps
      (Arlib.Computation.Charged.opMany
        (CountingMatroid.Model.Operations.Op.word instr) z result) = z := by
    cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  rw [hcost]
  unfold binaryRatLength binaryNatLength
  apply Nat.pow_le_pow_left
  omega



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
/-!
# Cost of the schedule tail

The setup phases have separate checked cost bounds. This module proves an exact
cost identity for the charged powers, observation count, draw width, and confidence
repetition computation, and bounds their sum by the prescribed polynomial.
Intermediate encoding lengths are bounded using the shared length and capped-search
lemmas in `ScheduleCostPrimitives`.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The remaining charged schedule operations have a polynomial
nonoracle charge after the opening and thermal setup phases.
TEXLINE: main.tex:1348-1358 -/
theorem solution (n r : ℕ) (p : InputParams) :
    let S := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1
    let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
    let L := 2 * n * (n + b)
    let D := 32 * (L + 1)
    otherSteps (thermalRest n p
      ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, p.ε / (D : ℚ)⟩) ≤
      10 ^ 150 * S ^ 40 := by
  have hceil_cost (q : ℚ) : otherSteps (CountingMatroid.Model.Operations.rationalCeil q) =
      (q.num.natAbs.log2 + q.den.log2 + 3) ^ 2 := by
    simp [CountingMatroid.Model.Operations.rationalCeil, otherSteps,
      Arlib.Computation.Op.all, Arlib.Computation.CostVec.many]
    rfl
  have hpowlog (base exponent : ℕ) :
      (CountingMatroid.Program.natPower base exponent).val.log2 ≤
        exponent * (base.log2 + 1) := by
    have hfold (l : List ℕ) (acc : ℕ) :
        (Arlib.Computation.Charged.foldl
          (fun acc _ => CountingMatroid.Model.Operations.natMul acc base) l acc).val.log2 ≤
          acc.log2 + l.length * (base.log2 + 1) := by
      induction l generalizing acc with
      | nil => simp
      | cons x xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons]
        have h := ih (acc * base)
        have hm := log2_mul_le acc base
        simpa only [CountingMatroid.Model.Operations.natMul,
          Arlib.Computation.Charged.val_op, List.length_cons] using
          (h.trans (by nlinarith :
            (acc * base).log2 + xs.length * (base.log2 + 1) ≤
              acc.log2 + (xs.length + 1) * (base.log2 + 1)))
    simpa [CountingMatroid.Program.natPower, Arlib.Computation.Charged.repeatFor,
      show (1 : ℕ).log2 = 0 from rfl]
      using hfold (List.range exponent) 1
  let S := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹) + 1
  let X := S ^ 2
  let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
  let L := 2 * n * (n + b)
  let D := 32 * (L + 1)
  let eta := p.ε / (D : ℚ)
  let A := 10000000000 * (L + 1) * (CountingMatroid.Program.natPower n 14).val
  let R := 2000 * (CountingMatroid.Program.natPower (L + 1) 2).val *
    (CountingMatroid.Program.natPower n 2).val *
    (20 * (CountingMatroid.Program.natPower n 4).val * (n * (L + 1) + 2))
  let Q := (A : ℚ) / (eta * eta)
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hn : n ≤ S := by dsimp [S]; omega
  have he : binaryRatLength p.ε ≤ S := by dsimp [S, binaryInputLength]; omega
  have hd : binaryRatLength p.δ ≤ S := by dsimp [S, binaryInputLength]; omega
  have hSX : S ≤ X := by dsimp [X]; nlinarith
  have hX : 1 ≤ X := by omega
  have hlog (a : ℕ) : a.log2 ≤ a := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 a
  have hb : b ≤ S + 15 := by
    have h := leastHalvings_value_le (p.ε / 10)
    have hlen := binaryRatLength_div_le p.ε 10
    have hten : binaryRatLength (10 : ℚ) = 7 := by decide
    rw [hten] at hlen
    dsimp [b]
    unfold binaryRatLength binaryNatLength at he hlen
    omega
  have hL : L ≤ 34 * X := by
    have hnb : n + b ≤ 17 * S := by omega
    calc
      L ≤ (2 * S) * (17 * S) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hnb
      _ = 34 * X := by dsimp [X]; ring
  have hL1 : (L + 1).log2 ≤ 35 * X := by have := hlog (L + 1); omega
  have hLl : L.log2 ≤ 34 * X := (hlog L).trans hL
  have hDl : D.log2 ≤ 1120 * X := by
    have := hlog D
    dsimp [D] at this ⊢
    omega
  have hnl : n.log2 ≤ X := (hlog n).trans (hn.trans hSX)
  have hAl : A.log2 ≤ 100 * X := by
    have h1 := log2_mul_le 10000000000 (L + 1)
    have h2 := log2_mul_le (10000000000 * (L + 1))
      (CountingMatroid.Program.natPower n 14).val
    have hp := hpowlog n 14
    have hc : (10000000000 : ℕ).log2 = 33 := by decide
    dsimp [A]
    omega
  have hRl : R.log2 ≤ 150 * X := by
    have h1 := log2_mul_le 2000 (CountingMatroid.Program.natPower (L + 1) 2).val
    have h2 := log2_mul_le
      (2000 * (CountingMatroid.Program.natPower (L + 1) 2).val)
      (CountingMatroid.Program.natPower n 2).val
    have h3 := log2_mul_le 20 (CountingMatroid.Program.natPower n 4).val
    have h4 := log2_mul_le n (L + 1)
    have h5 := log2_add_le (n * (L + 1)) 2
    have h6 := log2_mul_le (20 * (CountingMatroid.Program.natPower n 4).val)
      (n * (L + 1) + 2)
    have h7 := log2_mul_le
      (2000 * (CountingMatroid.Program.natPower (L + 1) 2).val *
        (CountingMatroid.Program.natPower n 2).val)
      (20 * (CountingMatroid.Program.natPower n 4).val * (n * (L + 1) + 2))
    have hp1 := hpowlog (L + 1) 2
    have hp2 := hpowlog n 2
    have hp4 := hpowlog n 4
    have hc1 : (2000 : ℕ).log2 = 10 := by decide
    have hc2 : (20 : ℕ).log2 = 4 := by decide
    have hc3 : (2 : ℕ).log2 = 1 := by decide
    dsimp [R]
    omega
  have heta : binaryRatLength eta ≤ 1125 * X := by
    have h := binaryRatLength_div_le p.ε (D : ℚ)
    rw [binaryRatLength_natCast] at h
    dsimp [eta]
    omega
  have heta2 : binaryRatLength (eta * eta) ≤ 2250 * X := by
    have := binaryRatLength_mul_le eta eta
    omega
  have hQ : binaryRatLength Q ≤ 2400 * X := by
    have := observationQuotient_length_le A D p.ε
    dsimp [Q, eta]
    omega
  have hdrawLog : (3 * L *
      (R + (CountingMatroid.Model.Operations.rationalCeil Q).val)).log2 ≤ 2600 * X := by
    have h1 := log2_mul_le 3 L
    have h2 := log2_add_le R (CountingMatroid.Model.Operations.rationalCeil Q).val
    have h3 := log2_mul_le (3 * L)
      (R + (CountingMatroid.Model.Operations.rationalCeil Q).val)
    have h4 := rationalCeil_log2_le Q
    have hc : (3 : ℕ).log2 = 1 := by decide
    omega
  have hmul : otherSteps (CountingMatroid.Model.Operations.ratMul eta eta) ≤
      9000000 * S ^ 4 := by
    have h := rationalBinary_otherSteps_le .mul eta eta (eta * eta)
    have hs : (binaryRatLength eta + binaryRatLength eta) ^ 2 ≤ (3000 * X) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have heq : (3000 * X) ^ 2 = 9000000 * S ^ 4 := by dsimp [X]; ring
    exact h.trans (hs.trans_eq heq)
  have hdiv : otherSteps (CountingMatroid.Model.Operations.ratDiv (A : ℚ) (eta * eta)) ≤
      9000000 * S ^ 4 := by
    have h := rationalBinary_otherSteps_le .udiv (A : ℚ) (eta * eta) Q
    have hlen : binaryRatLength (A : ℚ) + binaryRatLength (eta * eta) ≤ 3000 * X := by
      rw [binaryRatLength_natCast]
      omega
    have hs := Nat.pow_le_pow_left hlen 2
    have heq : (3000 * X) ^ 2 = 9000000 * S ^ 4 := by dsimp [X]; ring
    exact h.trans (hs.trans_eq heq)
  have hceil : otherSteps (CountingMatroid.Model.Operations.rationalCeil Q) ≤
      9000000 * S ^ 4 := by
    rw [hceil_cost]
    have hlen : Q.num.natAbs.log2 + Q.den.log2 + 3 ≤ 3000 * X := by
      unfold binaryRatLength binaryNatLength at hQ
      omega
    calc
      _ ≤ (3000 * X) ^ 2 := Nat.pow_le_pow_left hlen 2
      _ = 9000000 * S ^ 4 := by dsimp [X]; ring
  have hdraw : otherSteps (CountingMatroid.Program.leastDrawTrials
      (3 * L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))) ≤
        8000 * X := by
    have := leastDrawTrials_otherSteps_le
      (3 * L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))
    omega
  have hdelta : otherSteps (CountingMatroid.Program.leastHalvings p.δ) ≤
      300000 * S ^ 4 := by
    have hden : p.δ.den.log2 ≤ S := by
      unfold binaryRatLength binaryNatLength at hd
      omega
    have h := LeastHalvingsCost.leastHalvings_otherSteps_le p.δ
    have h1 : p.δ.den.log2 + 8 ≤ 9 * S := by omega
    have h2 : binaryRatLength p.δ + p.δ.den.log2 + 16 ≤ 18 * S := by omega
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 100 h1)
      (Nat.pow_le_pow_left h2 2)
    have heq : 100 * (9 * S) * (18 * S) ^ 2 = 291600 * S ^ 3 := by ring
    rw [heq] at hprod
    have h34 : S ^ 3 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide)
    have h4 : 1 ≤ S ^ 4 := one_le_pow₀ hS
    omega
  change otherSteps (thermalRest n p
    ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, eta⟩) ≤
      10 ^ 150 * S ^ 40
  rw [thermalRest_cost_eq]
  simp only [natPower_otherSteps_eq]
  change 4 + 2 + 2 + 14 + 14 + (A.log2 + 1) +
    otherSteps (CountingMatroid.Model.Operations.ratMul eta eta) +
    otherSteps (CountingMatroid.Model.Operations.ratDiv (A : ℚ) (eta * eta)) +
    otherSteps (CountingMatroid.Model.Operations.rationalCeil Q) +
    otherSteps (CountingMatroid.Program.leastDrawTrials
      (3 * L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))) +
    otherSteps (CountingMatroid.Program.leastHalvings p.δ) ≤ 10 ^ 150 * S ^ 40
  have hX40 : X ≤ S ^ 40 := pow_le_pow_right₀ hS (by decide)
  have h440 : S ^ 4 ≤ S ^ 40 := pow_le_pow_right₀ hS (by decide)
  have h40 : 1 ≤ S ^ 40 := one_le_pow₀ hS
  omega
