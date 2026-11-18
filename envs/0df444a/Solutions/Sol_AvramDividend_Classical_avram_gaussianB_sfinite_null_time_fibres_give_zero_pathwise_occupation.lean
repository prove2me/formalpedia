-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_sfinite_null_time_fibres_give_zero_pathwise_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:06:26.296927+00:00
-- url     : https://prove2.me/submissions/17d34c91-9a8d-4c7e-a924-4e0d543e7735

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section
/-- Original Gaussian null time fibres imply a.e. zero contact time. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) = 0) :
    ∀ᵐ ω ∂P, volume ((fun t : ℝ => (ω, t)) ⁻¹' S) = 0 := by
  have hZero : (P.prod volume) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    simp only [hFibre, lintegral_zero]
  exact Measure.measure_ae_null_of_prod_null hZero
