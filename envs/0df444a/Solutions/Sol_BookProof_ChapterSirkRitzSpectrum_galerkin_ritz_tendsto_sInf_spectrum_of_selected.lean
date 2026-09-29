-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.galerkin_ritz_tendsto_sInf_spectrum_of_selected
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:50:08.474972+00:00
-- url     : https://prove2.me/submissions/36b804f2-be9e-4228-a5af-11d9aea4f9b5

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.galerkin_ritz_tendsto_sInf_spectrum_of_selected
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzInf_tendsto_sInf_spectrum
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterYangMillsFriedrichs
import Theorems.Thm_BookProof_HermiteGalerkin_finiteModeRestrict_selects_operator
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] (A : F →L[ℂ] F)
    (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re)
    (b : HilbertBasis ℕ ℂ F) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A b) (topRestrict A) ∧
      Tendsto (fun m : ℕ => ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1))) atTop
        (nhds (sInf (spectrum ℝ A))) :=
  ⟨(finiteModeRestrict_selects_operator A hsa hpos b).1,
      ritzInf_tendsto_sInf_spectrum A hsa hpos b⟩
