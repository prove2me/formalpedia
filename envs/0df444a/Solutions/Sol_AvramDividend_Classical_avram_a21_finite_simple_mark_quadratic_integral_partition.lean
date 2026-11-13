-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_finite_simple_mark_quadratic_integral_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:17:31.932198+00:00
-- url     : https://prove2.me/submissions/8ef4d8f4-850c-4bfd-8255-f7462cab6af9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- The square of a simple mark decomposes over its original measurable fibres. -/
theorem solution
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : ν S < ⊤) (u : SimpleFunc ℝ ℝ) :
    (∫ z in S, (u z) ^ 2 ∂ν) =
      ∑ y ∈ u.range, y ^ 2 * (ν (S ∩ u ⁻¹' {y})).toReal := by
  classical
  let μ : Measure ℝ := ν.restrict S
  have hμ : μ Set.univ < ⊤ := by simpa [μ] using hMass
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  have hIy (y : ℝ) :
      Integrable ((u ⁻¹' {y}).indicator (fun _ : ℝ => y ^ 2)) μ :=
    (integrable_const (y ^ 2)).indicator (u.measurableSet_fiber y)
  have hPt (z : ℝ) : (u z) ^ 2 =
      ∑ y ∈ u.range, (u ⁻¹' {y}).indicator (fun _ : ℝ => y ^ 2) z := by
    have hz : u z ∈ u.range := u.mem_range_self z
    simp [Set.indicator, Finset.sum_ite_eq, hz]
  calc
    (∫ z in S, (u z) ^ 2 ∂ν) = ∫ z, (u z) ^ 2 ∂μ := rfl
    _ = ∫ z, ∑ y ∈ u.range, (u ⁻¹' {y}).indicator (fun _ : ℝ => y ^ 2) z ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with z
          exact hPt z
    _ = ∑ y ∈ u.range, ∫ z, (u ⁻¹' {y}).indicator (fun _ : ℝ => y ^ 2) z ∂μ :=
          integral_finset_sum u.range (by intro y hy; exact hIy y)
    _ = ∑ y ∈ u.range, y ^ 2 * (ν (S ∩ u ⁻¹' {y})).toReal := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [integral_indicator_const (y ^ 2) (u.measurableSet_fiber y)]
          rw [Measure.real_def]
          rw [Measure.restrict_apply (u.measurableSet_fiber y)]
          rw [Set.inter_comm]
          simp only [smul_eq_mul]
          ring
