-- Prove2me | solution 2 for BookProof.BandEnclosure.shiftInvert_widths_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T23:02:29.438254+00:00
-- url     : https://prove2.me/submissions/605c968d-31a2-4680-bd25-d7f28ab6190e

-- Generated from ChapterBandEnclosure.lean — solution of BookProof.BandEnclosure.shiftInvert_widths_tendsto_zero
import Mathlib
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFriedrichsFormGap
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
open BookProof.BandEnclosure











noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8















open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]













open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {lo hi : ℕ → ℝ} {nu gam : ℝ} (hnu : nu ≠ 0)
    (hlo : Tendsto lo atTop (𝓝 nu)) (hhi : Tendsto hi atTop (𝓝 nu)) :
    Tendsto (fun m => ((lo m)⁻¹ - gam) - ((hi m)⁻¹ - gam)) atTop (𝓝 0) := by

  have h1 : Tendsto (fun m => (lo m)⁻¹) atTop (𝓝 nu⁻¹) := hlo.inv₀ hnu
  have h2 : Tendsto (fun m => (hi m)⁻¹) atTop (𝓝 nu⁻¹) := hhi.inv₀ hnu
  have := (h1.sub_const gam).sub (h2.sub_const gam)
  simpa using this
