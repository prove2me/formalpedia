-- Prove2me | solution 1 for FamousTheorems.doob_decomposition_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:53:00.773494+00:00
-- url     : https://prove2.me/submissions/1bf65acf-442f-44f8-9f79-a2c9f6b85cb6

import Mathlib

open MeasureTheory

theorem solution {Ω E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ℱ : Filtration ℕ m0} [SigmaFiniteFiltration μ ℱ] {f : ℕ → Ω → E}
    (hf : StronglyAdapted ℱ f) (hfint : ∀ n, Integrable (f n) μ) :
    ∃ M A : ℕ → Ω → E, Martingale M ℱ μ ∧ StronglyAdapted ℱ (fun n => A (n + 1)) ∧ A 0 = 0 ∧ f = M + A :=
  ⟨martingalePart f ℱ μ, predictablePart f ℱ μ, martingale_martingalePart hf hfint,
    stronglyAdapted_predictablePart, predictablePart_zero, (martingalePart_add_predictablePart ℱ μ f).symm⟩
