-- Prove2me | solution 1 for BookProof.HermiteBandHigher.IsBandDeg.comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:51:05.542965+00:00
-- url     : https://prove2.me/submissions/1fb4ab70-23a4-4036-a11d-1deee8e434a7

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.IsBandDeg.comp
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_comp
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {m₁ m₂ : ℕ} {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hU : IsBandDeg m₂ U) (hT : IsBandDeg m₁ T) : IsBandDeg (m₁ + m₂) (U ∘ₗ T) := by

  obtain ⟨r₁, h₁⟩ := hT
  obtain ⟨r₂, h₂⟩ := hU
  exact ⟨r₁ + r₂, h₂.comp h₁⟩
