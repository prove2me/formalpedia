-- Prove2me | solution 1 for BookProof.HermiteGalerkin.isUnit_algebraMap_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:58:55.039945+00:00
-- url     : https://prove2.me/submissions/029d36a2-e8cf-45ff-ac6f-d5a6c140c1d7

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — solution of BookProof.HermiteGalerkin.isUnit_algebraMap_sub
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin













open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (algebraMap ℂ (F →L[ℂ] F) z - T) := by

  have hspec : z ∉ spectrum ℂ T := by
    intro hmem
    exact hz (by rw [← hT.spectrumRestricts.rightInvOn hmem]; simp)
  simpa [spectrum.mem_iff] using hspec
