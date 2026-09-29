-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T09:58:00.383343+00:00
-- url     : https://prove2.me/submissions/fb246979-6fa5-4d83-99db-7b7cb3f17cf9

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_sInf_spectrum_eq_rayleighInf
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzInf_finiteModeDomain_eq_rayleighInf
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterYangMillsFriedrichs
import Theorems.Thm_BookProof_HermiteGalerkin_ritzInf_tendsto_domainInf

open BookProof.FarisLavine
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A)
    (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) :
    Tendsto (fun m : ℕ => ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1))) atTop
      (nhds (sInf (spectrum ℝ A))) := by

  have hq : ∀ x : finiteModeDomain b, 0 ≤ quadForm (finiteModeRestrict A b) x :=
    fun x => hpos _
  have hlim := ritzInf_tendsto_domainInf b (finiteModeRestrict A b) hq
  rw [sInf_spectrum_eq_rayleighInf A hsa, ← ritzInf_finiteModeDomain_eq_rayleighInf A b]
  exact hlim
