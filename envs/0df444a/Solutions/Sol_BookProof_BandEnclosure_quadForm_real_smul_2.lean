-- Prove2me | solution 2 for BookProof.BandEnclosure.quadForm_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T22:42:45.751165+00:00
-- url     : https://prove2.me/submissions/c0983291-3c4e-46ca-b2c4-b2977778c9ad

-- Generated from ChapterBandEnclosure.lean — solution of BookProof.BandEnclosure.quadForm_real_smul
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
theorem solution {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ) (x : D) :
    quadForm H ((c : ℂ) • x) = c ^ 2 * quadForm H x := by

  have h : (inner ℂ (((c : ℂ) • x : D) : F) (H ((c : ℂ) • x)) : ℂ)
      = ((c ^ 2 : ℝ) : ℂ) * inner ℂ (x : F) (H x) := by
    rw [map_smul, Submodule.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  rw [quadForm, quadForm, h, Complex.re_ofReal_mul]
