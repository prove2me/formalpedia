-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_bounded_Borel_mark_first_second_integral_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:23:08.381205+00:00
-- url     : https://prove2.me/submissions/b41c0a29-3ee2-4859-9a94-6ea14db0169e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : ν S < ⊤) (g : ℝ → ℝ)
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1)
    (hLimit : ∀ z ∈ S,
      Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    Tendsto (fun k => ∫ z in S, f k z ∂ν)
      atTop (𝓝 (∫ z in S, g z ∂ν)) ∧
    Tendsto (fun k => ∫ z in S, (f k z) ^ 2 ∂ν)
      atTop (𝓝 (∫ z in S, (g z) ^ 2 ∂ν)) := by
  have hOne : Integrable (fun _ : ℝ => (1 : ℝ)) (ν.restrict S) := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ)) S ν
    apply Measure.integrableOn_of_bounded (M := 1) (ne_of_lt hMass)
      measurable_const.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hS] with z hz
    norm_num
  have hMeas (k : ℕ) :
      AEStronglyMeasurable (fun z : ℝ => f k z) (ν.restrict S) :=
    (f k).measurable.aestronglyMeasurable
  have hDom (k : ℕ) : ∀ᵐ z ∂ν.restrict S,
      ‖f k z‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    simpa only [Real.norm_eq_abs] using hBound k z hz
  have hLim : ∀ᵐ z ∂ν.restrict S,
      Tendsto (fun k => f k z) atTop (𝓝 (g z)) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact hLimit z hz
  have hDomSq (k : ℕ) : ∀ᵐ z ∂ν.restrict S,
      ‖(f k z) ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [hDom k] with z hz
    rw [norm_pow]
    nlinarith [mul_nonneg (sub_nonneg.mpr hz)
      (norm_nonneg (f k z))]
  have hLimSq : ∀ᵐ z ∂ν.restrict S,
      Tendsto (fun k => (f k z) ^ 2)
        atTop (𝓝 ((g z) ^ 2)) := by
    filter_upwards [hLim] with z hz
    exact hz.pow 2
  constructor
  · change Tendsto
      (fun k => ∫ z, f k z ∂ν.restrict S)
      atTop (𝓝 (∫ z, g z ∂ν.restrict S))
    exact tendsto_integral_of_dominated_convergence
      (fun _ => (1 : ℝ)) hMeas hOne hDom hLim
  · change Tendsto
      (fun k => ∫ z, (f k z) ^ 2 ∂ν.restrict S)
      atTop (𝓝 (∫ z, (g z) ^ 2 ∂ν.restrict S))
    exact tendsto_integral_of_dominated_convergence
      (fun _ => (1 : ℝ)) (fun k => (hMeas k).pow 2)
      hOne hDomSq hLimSq
