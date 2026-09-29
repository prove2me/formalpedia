-- Prove2me | solution 1 for FamousTheorems.levy_borel_cantelli
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:07:58.292838+00:00
-- url     : https://prove2.me/submissions/149003c1-b186-40ed-8de1-5513f8a63c50

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℕ m0} (μ : Measure Ω) [IsFiniteMeasure μ]
    {s : ℕ → Set Ω} (hs : ∀ n, @MeasurableSet Ω (ℱ n) (s n)) :
    ∀ᵐ ω ∂μ, ω ∈ Filter.limsup s Filter.atTop ↔
      Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k]) ω)
        Filter.atTop Filter.atTop :=
  ae_mem_limsup_atTop_iff μ hs
