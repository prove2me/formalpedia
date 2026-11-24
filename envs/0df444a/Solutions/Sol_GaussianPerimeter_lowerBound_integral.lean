-- Prove2me | solution 1 for GaussianPerimeter.lowerBound_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:26:40.144329+00:00
-- url     : https://prove2.me/submissions/e7bd1876-eef6-471a-8b99-597d5ad55023

module
public import Definitions.Def_GaussianPerimeter_Quadrature
public import Definitions.Def_GaussianPerimeter_Prefactor
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GaussianPerimeter_QuadratureCertificate
public import Theorems.Thm_GaussianPerimeter_expLower_le_exp
public import Theorems.Thm_GaussianPerimeter_exp_le_expUpper
public import Theorems.Thm_GaussianPerimeter_lowerBound_integral_of_trapezoidal

section
public section
open Finset
namespace GaussianPerimeter
local notation "A" => (6131 / 5000)
local notation "B" => (2387 / 1000)
local notation "F" => lowerBoundIntegrand A B
private theorem sample_le (i : ℕ) (hi : i < 10239) :
    (sample i : ℝ) / 1000000000 ≤ F (-(15 / 4) + ((i : ℝ) + 1) / 2048) := by
  have hiRat : (i : ℚ) ≤ 10239 := by exact_mod_cast hi.le
  have hiRat₀ : (0 : ℚ) ≤ i := by positivity
  have harg : |(A : ℚ) ^ 2 * gridPoint i| ≤ 32 := by
    unfold gridPoint
    rw [abs_le]
    norm_num
    constructor <;> linarith only [hiRat, hiRat₀]
  have hUpper := exp_le_expUpper harg
  let x := gridPoint i
  have hx : (x : ℝ) = -(15 / 4) + ((i : ℝ) + 1) / 2048 := by
    dsimp [x, gridPoint]
    push_cast
    rfl
  have hFloor := Int.floor_le (1000000000 * expLower (-x ^ 2 - B * expUpper (A ^ 2 * x)))
  have hFloor' : (sample i : ℝ) ≤
      (1000000000 : ℝ) * (expLower (-x ^ 2 - B * expUpper (A ^ 2 * x)) : ℝ) := by
    rw [sample, if_pos hi]
    exact_mod_cast hFloor
  have hOuter := expLower_le_exp (-x ^ 2 - B * expUpper (A ^ 2 * x))
  rw [← hx, lowerBoundIntegrand]
  refine ((div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2 (by
    simpa [mul_comm] using hFloor')).trans (hOuter.trans (Real.exp_le_exp.mpr ?_))
  push_cast at hUpper ⊢
  gcongr
private theorem sumSamples_eq (start n : ℕ) :
    sumSamples start n = ∑ i ∈ range n, sample (start + i) := by
  induction n with
  | zero => simp [sumSamples]
  | succ n ih => rw [sumSamples, sum_range_succ, ih]
private theorem sumBuckets_eq (n : ℕ) :
    sumBuckets n = ∑ i ∈ range (320 * n), sample i := by
  induction n with
  | zero => simp [sumBuckets]
  | succ n ih =>
    rw [sumBuckets, ih, sumSamples_eq, Nat.mul_succ, sum_range_add]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem bucketLower_le (k : ℕ) (hk : k < 32) :
    bucketLower k ≤ sumSamples (320 * k) 320 := by
  interval_cases k <;> decide +kernel
private theorem sumBounds_le (n : ℕ) (hn : n ≤ 32) : sumBounds n ≤ sumBuckets n := by
  induction n with
  | zero => simp [sumBounds, sumBuckets]
  | succ n ih =>
    rw [sumBounds, sumBuckets]
    exact add_le_add (ih (Nat.le_of_succ_le hn)) (bucketLower_le n hn)
private theorem sumSamples_bound : (682202112000 : ℤ) ≤ sumBuckets 32 :=
  (show (682202112000 : ℤ) ≤ sumBounds 32 by decide +kernel).trans
    (sumBounds_le 32 (by decide))
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open GaussianPerimeter
local notation "A" => (6131 / 5000)
local notation "B" => (2387 / 1000)
local notation "F" => lowerBoundIntegrand A B
namespace GaussianPerimeter
theorem _root_.solution :
    (0.333104 : ℝ) ≤ ∫ x in (-6 : ℝ)..6, F x := by
  apply lowerBound_integral_of_trapezoidal
  have hSum := sumSamples_bound
  rw [sumBuckets_eq, show (320 * 32 : ℕ) = 10239 + 1 by rfl, sum_range_succ,
    show sample 10239 = 0 by rfl, add_zero] at hSum
  have hSum' : (682202112000 : ℝ) ≤ ∑ i ∈ range 10239, (sample i : ℝ) := by
    exact_mod_cast hSum
  have hf : ∀ i ∈ range 10239,
      (sample i : ℝ) / 1000000000 ≤
      F (-(15 / 4) + ((i : ℝ) + 1) / 2048) :=
    fun i hi => sample_le i (mem_range.mp hi)
  have hm : (∑ i ∈ range 10239, (sample i : ℝ)) / 1000000000 ≤
      ∑ i ∈ range 10239, F (-(15 / 4) + ((i : ℝ) + 1) / 2048) := by
    rw [div_eq_mul_inv, sum_mul]
    exact sum_le_sum fun i hi => by
      rw [← div_eq_mul_inv]
      exact hf i hi
  rw [trapezoidal_integral]
  change (0.3331065 : ℝ) ≤
    ((5 / 4 - -(15 / 4)) / 10240) *
      ((F (-(15 / 4)) + F (5 / 4)) / 2 +
        ∑ i ∈ range 10239, F (-(15 / 4) + ((i : ℝ) + 1) * (5 / 4 - -(15 / 4)) / 10240))
  have hgrid (i : ℕ) :
      ((i : ℝ) + 1) * (5 / 4 - -(15 / 4)) / 10240 = ((i : ℝ) + 1) / 2048 := by ring
  simp_rw [hgrid]
  have hEnds : 0 ≤ (F (-(15 / 4)) + F (5 / 4)) / 2 := by
    unfold lowerBoundIntegrand
    positivity
  linarith only [hSum', hm, hEnds]
end GaussianPerimeter
