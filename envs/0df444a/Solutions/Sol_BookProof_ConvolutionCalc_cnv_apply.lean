-- Prove2me | solution 1 for BookProof.ConvolutionCalc.cnv_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:30:23.96198+00:00
-- url     : https://prove2.me/submissions/67a8506d-532e-4287-8eb3-961781c0b917

-- Generated from ChapterConvolutionCalc.lean — solution of BookProof.ConvolutionCalc.cnv_apply
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
theorem solution (u ρ : Vd d → ℂ) (x : Vd d) : cnv u ρ x = ∫ y, u y * ρ (x - y) := rfl
