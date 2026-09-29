-- Prove2me | solution 1 for FamousTheorems.riesz_subsequence_convergence_in_measure_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:44:36.823917+00:00
-- url     : https://prove2.me/submissions/98c5be3f-5bf0-4e86-bf27-0704c9125128

import Mathlib

theorem solution {α E : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [PseudoEMetricSpace E]
    {f : ℕ → α → E} {g : α → E} (hfg : MeasureTheory.TendstoInMeasure μ f Filter.atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Filter.Tendsto (fun i => f (ns i) x) Filter.atTop (nhds (g x)) :=
  hfg.exists_seq_tendsto_ae
