-- Prove2me | solution 1 for CountingLLL.RandomRAM.branching_expected_work
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:06:35.047246+00:00
-- url     : https://prove2.me/submissions/78cd6cc6-096b-42d0-bbc3-d1d98d56740f

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal

/-- The expected total size of a generation process with geometric offspring contraction. -/
theorem branching_total_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ≥0∞) (hZ : ∀ n, Measurable (Z n))
    (h0 : (∫⁻ ω, Z 0 ω ∂μ) ≤ 1)
    (hstep : ∀ n, (∫⁻ ω, Z (n+1) ω ∂μ) ≤ (1/8 : ℝ≥0∞) * (∫⁻ ω, Z n ω ∂μ)) :
    (∫⁻ ω, ∑' n, Z n ω ∂μ) ≤ (1 - (1/8 : ℝ≥0∞))⁻¹ := by
  have hgen : ∀ n, (∫⁻ ω, Z n ω ∂μ) ≤ (1/8 : ℝ≥0∞)^n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      calc
        _ ≤ (1/8 : ℝ≥0∞) * (∫⁻ ω, Z n ω ∂μ) := hstep n
        _ ≤ (1/8 : ℝ≥0∞) * (1/8 : ℝ≥0∞)^n := by gcongr
        _ = _ := by rw [pow_succ, mul_comm]
  rw [lintegral_tsum (fun n => (hZ n).aemeasurable)]
  calc
    _ ≤ ∑' n : ℕ, (1/8 : ℝ≥0∞)^n := ENNReal.tsum_le_tsum hgen
    _ = (1 - (1/8 : ℝ≥0∞))⁻¹ := ENNReal.tsum_geometric _
    _ = (1 - (1/8 : ℝ≥0∞))⁻¹ := by norm_num

theorem geometric_one_eighth : (1 - (1/8 : ℝ≥0∞))⁻¹ = (8/7 : ℝ≥0∞) := by
  have hbase : ((1 : ℝ≥0) - (1/8 : ℝ≥0)) = 7/8 := by
    apply NNReal.eq
    have hp : (1/8 : ℝ≥0) ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      norm_num
    rw [NNReal.coe_sub hp]
    norm_num
  have hcast := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hbase
  have heq : (1 - (1/8 : ℝ≥0∞)) = ((7/8 : ℝ≥0) : ℝ≥0∞) := by
    simpa [ENNReal.coe_sub, ENNReal.coe_div] using hcast
  rw [heq]
  rw [← ENNReal.coe_inv (by norm_num : (7/8 : ℝ≥0) ≠ 0)]
  have hinv : ((7/8 : ℝ≥0)⁻¹) = 8/7 := by norm_num
  rw [hinv]
  norm_num [ENNReal.coe_div]

theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z Work : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hZ : ∀ n, Measurable (Z n)) (hWork : ∀ n, Measurable (Work n))
    (h0 : (∫⁻ ω, Z 0 ω ∂μ) ≤ 1)
    (hstep : ∀ n, (∫⁻ ω, Z (n+1) ω ∂μ) ≤ (1/8 : ℝ≥0∞) * (∫⁻ ω, Z n ω ∂μ))
    (hcost : ∀ n, (∫⁻ ω, Work n ω ∂μ) ≤ C * (∫⁻ ω, Z n ω ∂μ)) :
    (∫⁻ ω, ∑' n, Z n ω ∂μ) ≤ (8/7 : ℝ≥0∞) ∧
    (∫⁻ ω, ∑' n, Work n ω ∂μ) ≤ C * (8/7 : ℝ≥0∞) := by
  have htotal : (∫⁻ ω, ∑' n, Z n ω ∂μ) ≤ (8/7 : ℝ≥0∞) := by
    simpa only [geometric_one_eighth] using branching_total_bound μ Z hZ h0 hstep
  constructor
  · exact htotal
  · rw [lintegral_tsum (fun n => (hWork n).aemeasurable)]
    calc
      _ ≤ ∑' n, C * (∫⁻ ω, Z n ω ∂μ) := ENNReal.tsum_le_tsum hcost
      _ = C * ∑' n, (∫⁻ ω, Z n ω ∂μ) := ENNReal.tsum_mul_left
      _ = C * (∫⁻ ω, ∑' n, Z n ω ∂μ) := by rw [lintegral_tsum (fun n => (hZ n).aemeasurable)]
      _ ≤ C * (8/7 : ℝ≥0∞) := by gcongr
