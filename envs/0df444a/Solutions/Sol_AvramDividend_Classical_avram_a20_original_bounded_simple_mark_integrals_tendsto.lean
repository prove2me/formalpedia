-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_bounded_simple_mark_integrals_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:22:59.345591+00:00
-- url     : https://prove2.me/submissions/82f9a62d-11f5-498c-90ca-43f4882df308

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : μ (Ioc 0 T ×ˢ S) < ⊤)
    (g : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1)
    (hLimit : ∀ z ∈ S,
      Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    Tendsto
      (fun k => ∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂μ)
      atTop (𝓝 (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂μ)) := by
  let C : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ S
  have hC : MeasurableSet C := measurableSet_Ioc.prod hS
  have hOne : Integrable (fun _ : ℝ≥0 × ℝ => (1 : ℝ))
      (μ.restrict C) := by
    change IntegrableOn (fun _ : ℝ≥0 × ℝ => (1 : ℝ)) C μ
    apply Measure.integrableOn_of_bounded (M := 1) (ne_of_lt hMass)
      measurable_const.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hC] with p hp
    norm_num
  have hMeas (k : ℕ) :
      AEStronglyMeasurable (fun p : ℝ≥0 × ℝ => f k p.2)
        (μ.restrict C) :=
    ((f k).measurable.comp measurable_snd).aestronglyMeasurable
  have hDom (k : ℕ) : ∀ᵐ p ∂μ.restrict C,
      ‖f k p.2‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem hC] with p hp
    simpa only [Real.norm_eq_abs] using hBound k p.2 hp.2
  have hLim : ∀ᵐ p ∂μ.restrict C,
      Tendsto (fun k => f k p.2) atTop (𝓝 (g p.2)) := by
    filter_upwards [ae_restrict_mem hC] with p hp
    exact hLimit p.2 hp.2
  change Tendsto
    (fun k => ∫ p, f k p.2 ∂μ.restrict C)
    atTop (𝓝 (∫ p, g p.2 ∂μ.restrict C))
  exact tendsto_integral_of_dominated_convergence
    (fun _ => (1 : ℝ)) hMeas hOne hDom hLim
