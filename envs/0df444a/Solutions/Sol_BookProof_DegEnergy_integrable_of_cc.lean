-- Prove2me | solution 1 for BookProof.DegEnergy.integrable_of_cc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:39:08.80088+00:00
-- url     : https://prove2.me/submissions/927a036c-bdb8-4d06-961a-c8738bd867fe

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.integrable_of_cc
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

set_option maxHeartbeats 1000000 in
theorem solution {f : Vd d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (volume : Measure (Vd d)) := hf.integrable_of_hasCompactSupport hc
