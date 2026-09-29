-- Prove2me | solution 1 for FamousTheorems.doob_upcrossing_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:09:02.646698+00:00
-- url     : https://prove2.me/submissions/24a31f38-3242-409c-9200-3d124c62ed92

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {f : ℕ → Ω → ℝ} {ℱ : Filtration ℕ m0}
    [IsFiniteMeasure μ] (a b : ℝ) (hf : Submartingale f ℱ μ) (N : ℕ) :
    (b - a) * ∫ ω, (upcrossingsBefore a b f N ω : ℝ) ∂μ ≤ ∫ ω, (f N ω - a)⁺ ∂μ :=
  hf.mul_integral_upcrossingsBefore_le_integral_pos_part a b N
