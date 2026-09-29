-- Prove2me | solution 1 for FamousTheorems.first_moment_method
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:58:44.143727+00:00
-- url     : https://prove2.me/submissions/6ef65e7a-f9c3-4a31-840a-91eaffcabd43

import Mathlib

open MeasureTheory

theorem solution {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α} {f : α → ℝ} (hμ : μ s ≠ 0)
    (hμ' : μ s ≠ ⊤) (hf : IntegrableOn f s μ) : 0 < μ {x | x ∈ s ∧ f x ≤ ⨍ a in s, f a ∂μ} :=
  measure_le_setAverage_pos hμ hμ' hf
