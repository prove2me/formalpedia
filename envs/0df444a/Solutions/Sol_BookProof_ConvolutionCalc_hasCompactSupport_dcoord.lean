-- Prove2me | solution 1 for BookProof.ConvolutionCalc.hasCompactSupport_dcoord
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:20:44.828853+00:00
-- url     : https://prove2.me/submissions/2391702b-06b1-43a6-a03a-0ca2620f54fe

-- Generated from ChapterConvolutionCalc.lean — solution of BookProof.ConvolutionCalc.hasCompactSupport_dcoord
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ConvolutionCalc




open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {ρ : Vd d → ℂ}
    (hc : HasCompactSupport ρ) (j : Fin d) : HasCompactSupport (dcoord j ρ) := by

  refine (hc.fderiv ℝ).mono ?_
  intro x hx
  simp only [Function.mem_support, dcoord] at hx ⊢
  intro h
  exact hx (by rw [h]; simp)
