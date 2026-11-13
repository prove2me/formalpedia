-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:08:33.346572+00:00
-- url     : https://prove2.me/submissions/099e709b-ed7b-4e7c-a0aa-a3c18b5bed94

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (S : Set ℝ) (hS : MeasurableSet S)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hMass : μ (Ioc 0 T ×ˢ S) < ⊤)
    (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    IntegrableOn (fun p : ℝ≥0 × ℝ => g p.2)
      (Ioc 0 T ×ˢ S) μ ∧
    |∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂μ| ≤
      (μ (Ioc 0 T ×ˢ S)).toReal := by
  let C : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ S
  have hC : MeasurableSet C := measurableSet_Ioc.prod hS
  have hMeas : Measurable (fun p : ℝ≥0 × ℝ => g p.2) :=
    hg.comp measurable_snd
  have hPoint : ∀ p ∈ C, ‖g p.2‖ ≤ (1 : ℝ) := by
    intro p hp
    simpa only [Real.norm_eq_abs] using hBound p.2 hp.2
  have hAE : ∀ᵐ p ∂μ.restrict C, ‖g p.2‖ ≤ (1 : ℝ) :=
    (ae_restrict_mem hC).mono (fun p hp => hPoint p hp)
  have hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => g p.2) C μ :=
    Measure.integrableOn_of_bounded (ne_of_lt hMass)
      hMeas.aestronglyMeasurable hAE
  have hNorm := norm_setIntegral_le_of_norm_le_const
    (f := fun p : ℝ≥0 × ℝ => g p.2)
    (s := C) (μ := μ) (C := 1) hMass hPoint
  constructor
  · exact hInt
  · simpa only [C, Real.norm_eq_abs, Measure.real_def, one_mul] using hNorm
