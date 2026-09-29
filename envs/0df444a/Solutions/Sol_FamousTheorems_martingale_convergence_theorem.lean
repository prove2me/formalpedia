-- Prove2me | solution 1 for FamousTheorems.martingale_convergence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:09:27.147061+00:00
-- url     : https://prove2.me/submissions/4abd142a-9983-4c6b-a7e3-8c3255374cd7

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    {R : NNReal} [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Filter.Tendsto (fun n => f n ω) Filter.atTop (nhds c) :=
  hf.exists_ae_tendsto_of_bdd hbdd
