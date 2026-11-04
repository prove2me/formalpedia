-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_continuous_compact_test_integrable_on_finite_negative_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:05:17.772297+00:00
-- url     : https://prove2.me/submissions/a9192e59-9252-4fa1-ba62-cf267fb27713

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology

/-- A compact continuous test supported inside a finite-measure
    negative band is integrable even if the mark measure is infinite near zero. -/
theorem solution
    (μ : Measure ℝ) (g : ℝ → ℝ)
    (hcont : Continuous g) (hcompact : HasCompactSupport g)
    {ε : ℝ} (hμ : μ (Iic (-ε)) < ⊤)
    (hsupp : Function.support g ⊆ Iic (-ε)) :
    Integrable g μ := by
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcont
  have hsm : AEStronglyMeasurable g (μ.restrict (Iic (-ε))) :=
    hcont.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ.restrict (Iic (-ε)), ‖g x‖ ≤ C :=
    Filter.Eventually.of_forall hC
  have hlocal : IntegrableOn g (Iic (-ε)) μ :=
    IntegrableOn.of_bound hμ hsm C hbound
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hlocal
