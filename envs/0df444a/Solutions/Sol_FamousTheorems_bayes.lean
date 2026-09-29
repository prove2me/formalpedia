-- Prove2me | solution 1 for FamousTheorems.bayes
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T01:51:32.763408+00:00
-- url     : https://prove2.me/submissions/3170f19e-4eb9-4a2d-b3f6-94aef2fd8400

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} {s t : Set Ω}
    (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t :=
  ProbabilityTheory.cond_eq_inv_mul_cond_mul hms hmt μ
