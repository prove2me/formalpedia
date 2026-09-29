-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:58:47.361015+00:00
-- url     : https://prove2.me/submissions/c48e8866-f338-474f-a562-7e314ceda99d

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighSet_bddBelow
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzSet_subset_rayleighSet
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    BddBelow (ritzSet (finiteModeRestrict A b) (finiteModeDomain b)) := (rayleighSet_bddBelow A).mono (ritzSet_subset_rayleighSet A b)
