-- Prove2me | solution 1 for BookProof.HermiteBandHigher.IsBandDeg.add
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:48:30.162988+00:00
-- url     : https://prove2.me/submissions/8b08e9da-5ebf-4ec2-bda9-c7f12d0b00c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.IsBandDeg.add
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_Band_monoR
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_monoR
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_add
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : IsBandDeg m T) (hS : IsBandDeg m S) : IsBandDeg m (T + S) := by

  obtain ⟨r₁, h₁⟩ := hT
  obtain ⟨r₂, h₂⟩ := hS
  exact ⟨max r₁ r₂, (h₁.monoR (le_max_left _ _)).add (h₂.monoR (le_max_right _ _))⟩
