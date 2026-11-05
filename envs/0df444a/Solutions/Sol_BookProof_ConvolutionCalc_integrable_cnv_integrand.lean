-- Prove2me | solution 1 for BookProof.ConvolutionCalc.integrable_cnv_integrand
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:21:07.752382+00:00
-- url     : https://prove2.me/submissions/e3ded02b-6bea-4c0a-a881-5f8a51e0c26b

-- Generated from ChapterConvolutionCalc.lean — solution of BookProof.ConvolutionCalc.integrable_cnv_integrand
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
theorem solution {u g : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hg : Continuous g)
    (hgc : HasCompactSupport g) (x : Vd d) :
    Integrable (fun y => u y * g (x - y)) (volume : Measure (Vd d)) := hgc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ) hu hg x
