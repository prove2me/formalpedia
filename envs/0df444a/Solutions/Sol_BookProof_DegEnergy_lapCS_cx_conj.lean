-- Prove2me | solution 1 for BookProof.DegEnergy.lapCS_cx_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:30:43.335224+00:00
-- url     : https://prove2.me/submissions/359021b3-4ca4-40bd-a937-3bac883663c1

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.lapCS_cx_conj
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Theorems.Thm_BookProof_DegEnergy_lapCS_conj
import Theorems.Thm_BookProof_DegEnergy_contDiff_cx
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
theorem solution {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (S : Finset (Fin d)) (y : Vd d) :
    (starRingEnd ℂ) (lapCS S (cx χ) y) = lapCS S (cx χ) y := by

  rw [lapCS_conj (contDiff_cx hχ) S y]
  congr 1
  funext t
  simp [cx]
