-- Prove2me | solution 1 for BookProof.ConvolutionCalc.contDiff_cnv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:20:26.910348+00:00
-- url     : https://prove2.me/submissions/76d45468-acff-426a-a268-a1f3ca077be0

-- Generated from ChapterConvolutionCalc.lean — solution of BookProof.ConvolutionCalc.contDiff_cnv
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
theorem solution {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cnv u ρ) := hc.contDiff_convolution_right _ hu hρ
