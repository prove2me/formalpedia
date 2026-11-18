-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB158_finite_positive_horizon_measure_implies_finite_discounted_stopped_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:21:26.468625+00:00
-- url     : https://prove2.me/submissions/8bed128b-ce31-40ee-89dc-c00c22723947

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section
/-- Finite nonnegative horizon measure yields finite discounted cash. -/
theorem solution
    (μ : Measure ℝ) (q T : ℝ)
    (hq : 0 ≤ q) (hT : 0 ≤ T)
    (A : Set ℝ) (hA : A ⊆ Icc (0 : ℝ) T)
    (hMass : μ (Icc (0 : ℝ) T) ≠ ⊤) :
    (∫⁻ t in A,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≠ ⊤ := by
  have hSet :
      (∫⁻ t in A,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
      (∫⁻ t in Icc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) :=
    lintegral_mono_set hA
  have hWeight :
      (∫⁻ t in Icc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
      μ (Icc (0 : ℝ) T) := by
    calc
      _ ≤ (∫⁻ t in Icc (0 : ℝ) T, (1 : ℝ≥0∞) ∂μ) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have hMul : 0 ≤ q * t := mul_nonneg hq ht.1
        have hExp : Real.exp (-(q * t)) ≤ (1 : ℝ) :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr hMul)
        exact (ENNReal.ofReal_le_ofReal hExp).trans (by simp)
      _ = μ (Icc (0 : ℝ) T) := by simp
  intro hTop
  have hBound := hSet.trans hWeight
  rw [hTop] at hBound
  exact hMass (top_le_iff.mp hBound)
