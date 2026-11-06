-- Prove2me | solution 1 for BookProof.DegEnergy.norm_cx
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T17:38:07.90787+00:00
-- url     : https://prove2.me/submissions/f0e567e1-b739-462d-a92f-afdfd0246dc9

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.norm_cx
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
theorem solution (χ : Vd d → ℝ) (x : Vd d) : ‖cx χ x‖ = |χ x| := by
  simp only [cx]
  exact Complex.norm_real (χ x)
