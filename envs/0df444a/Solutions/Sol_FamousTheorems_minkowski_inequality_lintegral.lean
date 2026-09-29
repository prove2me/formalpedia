-- Prove2me | solution 1 for FamousTheorems.minkowski_inequality_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:06:57.200928+00:00
-- url     : https://prove2.me/submissions/f0fbe882-a56a-419c-b437-56703e000a20

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ} {f g : α → ENNReal}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hp1 : 1 ≤ p) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) :=
  ENNReal.lintegral_Lp_add_le hf hg hp1
