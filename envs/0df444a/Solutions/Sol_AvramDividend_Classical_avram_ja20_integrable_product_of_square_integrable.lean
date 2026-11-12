-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja20_integrable_product_of_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:34:20.71663+00:00
-- url     : https://prove2.me/submissions/e5c88655-af9d-4a6a-8ce9-8a506d70eda3

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G J : Ω → ℝ)
    (hGMeas : AEStronglyMeasurable G P)
    (hJMeas : AEStronglyMeasurable J P)
    (hGsq : Integrable (fun ω => (G ω) ^ 2) P)
    (hJsq : Integrable (fun ω => (J ω) ^ 2) P) :
    Integrable (fun ω => G ω * J ω) P := by
  have hBound : Integrable (fun ω => (G ω) ^ 2 + (J ω) ^ 2) P :=
    hGsq.add hJsq
  refine hBound.mono' (hGMeas.mul hJMeas) ?_
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (G ω + J ω),
      sq_nonneg (G ω), sq_nonneg (J ω)]
  · nlinarith [sq_nonneg (G ω - J ω),
      sq_nonneg (G ω), sq_nonneg (J ω)]
