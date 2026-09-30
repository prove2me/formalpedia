-- Prove2me | solution 2 for BookProof.BandEnclosure.shiftInvert_band_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T22:50:51.447915+00:00
-- url     : https://prove2.me/submissions/8c861e17-943d-415e-b94c-9a0dab8719ef

-- Generated from ChapterBandEnclosure.lean — solution of BookProof.BandEnclosure.shiftInvert_band_enclosure
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
theorem solution {lo hi : ℕ → ℝ} {nu lam gam : ℝ}
    (hlopos : ∀ m, 0 < lo m) (hband : ∀ m, nu ∈ Set.Icc (lo m) (hi m))
    (hmap : lam = nu⁻¹ - gam) :
    ∀ m, lam ∈ Set.Icc ((hi m)⁻¹ - gam) ((lo m)⁻¹ - gam) := by

  intro m
  obtain ⟨h1, h2⟩ := hband m
  have hnu : 0 < nu := lt_of_lt_of_le (hlopos m) h1
  subst hmap
  constructor
  · gcongr
  · gcongr
    exact hlopos m
