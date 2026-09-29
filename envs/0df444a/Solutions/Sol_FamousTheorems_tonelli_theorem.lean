-- Prove2me | solution 1 for FamousTheorems.tonelli_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:03:52.124559+00:00
-- url     : https://prove2.me/submissions/1ff11ab3-b4a0-43e1-ad53-f96fbf456471

import Mathlib

open MeasureTheory

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite ν] (f : α × β → ENNReal) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  MeasureTheory.lintegral_prod f hf
