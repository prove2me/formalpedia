-- Prove2me | solution 1 for FirstPassageLinearTransport.powerDense_of_shell_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:45.278152+00:00
-- url     : https://prove2.me/submissions/4017186d-873c-4877-8c49-00571ad3f137

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_badCount_le_shell_sum

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {S : Set ℕ} {K c : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hclt : c < Real.log 2)
    (hshell : ∀ M : ℕ,
      ((shellBad S M).card : ℝ) ≤
        K * Real.exp (-c * M) * (2 : ℝ) ^ M) :
    PowerDense S
      (2 * K / (2 * Real.exp (-c) - 1))
      (c / Real.log 2) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set r : ℝ := 2 * Real.exp (-c) with hr_def
  have hr1 : 1 < r := by
    have h2 : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
    have h : Real.exp (-Real.log 2) < Real.exp (-c) :=
      Real.exp_lt_exp.2 (by linarith)
    rw [h2] at h
    rw [hr_def]
    linarith
  have hrm1 : 0 < r - 1 := by linarith
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · rw [div_le_one hlog2]
    exact le_of_lt hclt
  intro X hX
  have hXpos : 0 < X := by omega
  set L := Nat.log 2 X with hL_def
  have hsum := badCount_le_shell_sum S X
  have hsumR :
      (badCount S X : ℝ) ≤
        ∑ M ∈ Finset.range (L + 1), ((shellBad S M).card : ℝ) := by
    exact_mod_cast hsum
  have hgeom :
      ∑ M ∈ Finset.range (L + 1), ((shellBad S M).card : ℝ) ≤
        K * ∑ M ∈ Finset.range (L + 1), r ^ M := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro M _
    have hrw : K * r ^ M =
        K * Real.exp (-c * M) * (2 : ℝ) ^ M := by
      rw [hr_def, mul_pow, ← Real.exp_nat_mul]
      ring_nf
    rw [hrw]
    exact hshell M
  have hgs :
      ∑ M ∈ Finset.range (L + 1), r ^ M =
        (r ^ (L + 1) - 1) / (r - 1) :=
    geom_sum_eq (by linarith) _
  have hgs' :
      ∑ M ∈ Finset.range (L + 1), r ^ M ≤
        r ^ (L + 1) / (r - 1) := by
    rw [hgs]
    gcongr
    linarith
  have hXL : (2 : ℝ) ^ L ≤ (X : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hXpos.ne'
  have hLX : (X : ℝ) < 2 ^ (L + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) X
  have hXRpos : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hpow2 : (2 : ℝ) ^ (L + 1) ≤ 2 * X := by
    rw [pow_succ]
    nlinarith [hXL]
  have hexp :
      Real.exp (-c) ^ (L + 1) ≤
        (X : ℝ) ^ (-(c / Real.log 2)) := by
    have hlnX : Real.log X ≤ ((L : ℝ) + 1) * Real.log 2 := by
      have h := Real.log_le_log hXRpos (le_of_lt hLX)
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hXRpos]
    apply Real.exp_le_exp.2
    have hmul :
        c / Real.log 2 * Real.log X ≤ ((L : ℝ) + 1) * c := by
      have h := mul_le_mul_of_nonneg_left hlnX
        (le_of_lt (div_pos hc hlog2))
      calc
        c / Real.log 2 * Real.log X ≤
            c / Real.log 2 * (((L : ℝ) + 1) * Real.log 2) := h
        _ = ((L : ℝ) + 1) * c := by field_simp
    push_cast
    nlinarith [hmul]
  have hrL :
      r ^ (L + 1) ≤
        2 * X * (X : ℝ) ^ (-(c / Real.log 2)) := by
    rw [hr_def, mul_pow]
    calc
      (2 : ℝ) ^ (L + 1) * Real.exp (-c) ^ (L + 1) ≤
          (2 * X) * Real.exp (-c) ^ (L + 1) :=
        mul_le_mul_of_nonneg_right hpow2 (by positivity)
      _ ≤ (2 * X) * (X : ℝ) ^ (-(c / Real.log 2)) := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hXrpow :
      (X : ℝ) * (X : ℝ) ^ (-(c / Real.log 2)) =
        (X : ℝ) ^ (1 - c / Real.log 2) := by
    rw [show (1 : ℝ) - c / Real.log 2 =
        1 + -(c / Real.log 2) by ring,
      Real.rpow_add hXRpos, Real.rpow_one]
  calc
    (badCount S X : ℝ) ≤ K * ∑ M ∈ Finset.range (L + 1), r ^ M :=
      hsumR.trans hgeom
    _ ≤ K * (r ^ (L + 1) / (r - 1)) :=
      mul_le_mul_of_nonneg_left hgs' hK.le
    _ ≤ K * ((2 * X * (X : ℝ) ^ (-(c / Real.log 2))) /
          (r - 1)) := by gcongr
    _ = 2 * K / (r - 1) *
          ((X : ℝ) * (X : ℝ) ^ (-(c / Real.log 2))) := by
      field_simp
    _ = 2 * K / (r - 1) * (X : ℝ) ^ (1 - c / Real.log 2) := by
      rw [hXrpow]
end FirstPassageLinearTransport
