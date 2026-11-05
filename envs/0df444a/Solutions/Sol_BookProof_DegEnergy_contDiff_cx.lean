-- Prove2me | solution 1 for BookProof.DegEnergy.contDiff_cx
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:30:35.671369+00:00
-- url     : https://prove2.me/submissions/5f467c46-10e7-4281-8d9a-900757cb3c44

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.contDiff_cx
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
theorem solution {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx χ) := Complex.ofRealCLM.contDiff.comp hχ
