-- Prove2me | solution 1 for BookProof.DegEnergy.integral_cx_sq_mul_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:30:46.960122+00:00
-- url     : https://prove2.me/submissions/9bb192fd-313c-4369-84f1-2e5bfcce18ae

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.integral_cx_sq_mul_normSq
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
theorem solution {χ : Vd d → ℝ} (v : Vd d → ℂ) :
    ∀ x : Vd d, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * v x
      = (((χ x) ^ 2 * ‖v x‖ ^ 2 : ℝ) : ℂ) := by

  intro x
  have h : (starRingEnd ℂ) (v x) * v x = ((‖v x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    norm_cast
  rw [mul_assoc, h]
  simp [cx]
