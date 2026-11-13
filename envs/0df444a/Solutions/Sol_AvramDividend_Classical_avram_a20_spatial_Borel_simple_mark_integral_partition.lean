-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_spatial_Borel_simple_mark_integral_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:19:03.801952+00:00
-- url     : https://prove2.me/submissions/32d26ee8-be6f-48cb-ba28-28641cf1e262

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (g : SimpleFunc ℝ ℝ)
    (hInt : IntegrableOn (fun z : ℝ => g z) S ν) :
    (∫ z in S, g z ∂ν) =
      ∑ y ∈ g.range, y * (ν (S ∩ g ⁻¹' {y})).toReal := by
  classical
  have hGI : Integrable (fun z : ℝ => g z) (ν.restrict S) := by
    change IntegrableOn (fun z : ℝ => g z) S ν
    exact hInt
  calc
    (∫ z in S, g z ∂ν) =
        ∑ y ∈ g.range, (ν.restrict S).real (g ⁻¹' {y}) • y :=
      SimpleFunc.integral_eq_sum g hGI
    _ = ∑ y ∈ g.range,
        y * (ν (S ∩ g ⁻¹' {y})).toReal := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Measure.real_def]
      rw [Measure.restrict_apply (g.measurableSet_fiber y)]
      rw [Set.inter_comm]
      simp only [smul_eq_mul]
      ring
