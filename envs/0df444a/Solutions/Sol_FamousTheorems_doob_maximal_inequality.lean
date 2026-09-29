-- Prove2me | solution 1 for FamousTheorems.doob_maximal_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:09:02.618366+00:00
-- url     : https://prove2.me/submissions/4c17804b-9c75-4dce-bd0c-362b369b80c3

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : NNReal} (n : ℕ) :
    (ε : ENNReal) * μ {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω},
        f n ω ∂μ) :=
  MeasureTheory.maximal_ineq hsub hnonneg n
