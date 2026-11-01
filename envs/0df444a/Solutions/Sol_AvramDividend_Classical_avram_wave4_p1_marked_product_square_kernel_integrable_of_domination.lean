-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_marked_product_square_kernel_integrable_of_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:16:08.508169+00:00
-- url     : https://prove2.me/submissions/95b7296b-08f8-4346-84f1-d7b067984ba9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (F : A × E → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : C < ∞)
    (hdom : ∀ p, F p ≤ C * g p.2) :
    ∫⁻ p, F p ∂μ.prod ν < ∞ := by
  have hupper :
      (∫⁻ p, F p ∂μ.prod ν) ≤
        (C * (∫⁻ z, g z ∂ν)) * μ Set.univ := by
    calc
      (∫⁻ p, F p ∂μ.prod ν) ≤
          ∫⁻ a, ∫⁻ z, F (a, z) ∂ν ∂μ :=
        lintegral_prod_le F
      _ ≤ ∫⁻ a, ∫⁻ z, C * g z ∂ν ∂μ := by
        apply lintegral_mono
        intro a
        apply lintegral_mono
        intro z
        exact hdom (a, z)
      _ = (C * (∫⁻ z, g z ∂ν)) * μ Set.univ := by
        simp only [lintegral_const_mul C hg, lintegral_const]
  have hμ : μ Set.univ < ∞ := measure_lt_top μ Set.univ
  have hfin : (C * (∫⁻ z, g z ∂ν)) * μ Set.univ < ∞ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hC henergy) hμ
  exact lt_of_le_of_lt hupper hfin
