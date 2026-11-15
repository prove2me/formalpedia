-- Prove2me | solution 1 for AvramDividend.Classical.arbitrary_measure_vitali_universal_claim_false_nat_universe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:56:51.278716+00:00
-- url     : https://prove2.me/submissions/78d335f5-bfb7-4a00-a6b5-9e2fb22b709a

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_counting_measure_uniform_integrability_counterexample_vitali
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
noncomputable section
theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ),
      UniformIntegrable Y 1 μ →
      (∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) →
      Integrable Z μ ∧
        Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
          (nhds (∫ ω, Z ω ∂μ))) := by
  intro h
  obtain ⟨Y, hUI, hPoint, hMean⟩ :=
    AvramDividend.Classical.counting_measure_uniform_integrability_counterexample_vitali
  have hAE : ∀ᵐ ω ∂(Measure.count : Measure ℕ),
      Tendsto (fun n => Y n ω) atTop (nhds ((fun _ : ℕ => (0 : ℝ)) ω)) :=
    Filter.Eventually.of_forall hPoint
  obtain ⟨_, hConv⟩ := h (Measure.count : Measure ℕ) Y
    (fun _ : ℕ => (0 : ℝ)) hUI hAE
  have hEq : (fun n => ∫ ω, Y n ω ∂(Measure.count : Measure ℕ)) =
      (fun _ : ℕ => (1 : ℝ)) := funext hMean
  rw [hEq] at hConv
  have hZero : (∫ ω : ℕ, (0 : ℝ) ∂(Measure.count : Measure ℕ)) = 0 := by
    simp
  rw [hZero] at hConv
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hConv)
