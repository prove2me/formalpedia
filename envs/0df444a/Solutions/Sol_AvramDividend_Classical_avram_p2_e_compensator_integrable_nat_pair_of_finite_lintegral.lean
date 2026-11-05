-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_integrable_nat_pair_of_finite_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:17:28.53753+00:00
-- url     : https://prove2.me/submissions/5706b55f-6a05-4765-bea7-1aa19bb571f0

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-- Finite ENNReal mean and source measurability imply real integrability of a pair count. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (K : Ω → ℕ)
    (hMeas : Measurable (fun ω => (K ω : ℝ≥0∞)))
    (hFinite : (∫⁻ ω, (K ω : ℝ≥0∞) ∂μ) < ⊤) :
    Integrable (fun ω => (K ω : ℝ)) μ := by
  have hMeasReal : Measurable (fun ω => (K ω : ℝ)) := by
    have hComp := ENNReal.measurable_toReal.comp hMeas
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using hComp
  have hNonneg : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ (K ω : ℝ) := by
    filter_upwards [] with ω
    positivity
  have hIntegral : HasFiniteIntegral (fun ω => (K ω : ℝ)) μ := by
    apply (hasFiniteIntegral_iff_ofReal hNonneg).2
    simpa using hFinite
  exact ⟨hMeasReal.aestronglyMeasurable, hIntegral⟩
