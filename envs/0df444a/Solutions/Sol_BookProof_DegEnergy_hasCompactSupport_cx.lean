-- Prove2me | solution 1 for BookProof.DegEnergy.hasCompactSupport_cx
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:30:39.42459+00:00
-- url     : https://prove2.me/submissions/77233c9e-6fb3-4857-850d-7c6947dac6f0

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.hasCompactSupport_cx
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterHermiteProductCore
open BookProof.DegEnergy




open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.ConvolutionCalc
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (S : Finset (Fin d))

set_option maxHeartbeats 1000000 in
theorem solution {χ : Vd d → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (cx χ) := by

  refine hχc.mono ?_
  intro x hx
  simp only [Function.mem_support, cx, ne_eq, Complex.ofReal_eq_zero] at hx ⊢
  exact hx
