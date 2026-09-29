-- Prove2me | solution 1 for FamousTheorems.law_of_unconscious_statistician
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:04:43.089997+00:00
-- url     : https://prove2.me/submissions/c68ff3b0-612f-42fd-8537-f4ed15f9fbaf

import Mathlib

open MeasureTheory

theorem solution {Ω E F : Type*} [MeasurableSpace E] {m : MeasurableSpace Ω} {P : Measure Ω} {μ : Measure E}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [IsFiniteMeasure P] {X : Ω → E} [HasPDF X P μ] {f : E → F}
    (hf : AEStronglyMeasurable f μ) :
    ∫ x, (pdf X P μ x).toReal • f x ∂μ = ∫ ω, f (X ω) ∂P :=
  pdf.integral_pdf_smul hf
