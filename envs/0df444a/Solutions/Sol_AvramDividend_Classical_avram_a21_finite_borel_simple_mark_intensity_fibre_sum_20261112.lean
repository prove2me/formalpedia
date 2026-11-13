-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:05:44.421872+00:00
-- url     : https://prove2.me/submissions/84ed3d13-f5e8-4f7b-a133-c3da52350d2f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_avram_a20_spatial_Borel_simple_mark_integral_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- An exact finite mark-fibre intensity partition at physical time T. -/
theorem solution
    (ν : Measure ℝ) (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hMass : ν S < ⊤)
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    (T : ℝ) * (∫ z in S, g z ∂ν) =
      ∑ y ∈ g.range, y *
        (((T : ℝ≥0∞) * ν (S ∩ g ⁻¹' {y})).toReal) := by
  classical
  have hMeas : AEStronglyMeasurable
      (fun z : ℝ => g z) (ν.restrict S) :=
    g.measurable.aestronglyMeasurable
  have hBoundAE : ∀ᵐ z ∂(ν.restrict S), ‖g z‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    simpa only [Real.norm_eq_abs] using hBound z hz
  have hInt : IntegrableOn (fun z : ℝ => g z) S ν :=
    IntegrableOn.of_bound hMass hMeas 1 hBoundAE
  rw [avram_a20_spatial_Borel_simple_mark_integral_partition
    ν S hS g hInt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [ENNReal.toReal_mul]
  have ht : (T : ℝ≥0∞).toReal = (T : ℝ) := by simp
  rw [ht]
  ring
