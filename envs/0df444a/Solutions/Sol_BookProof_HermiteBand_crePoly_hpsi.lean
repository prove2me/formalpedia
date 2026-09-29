-- Prove2me | solution 1 for BookProof.HermiteBand.crePoly_hpsi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:05:00.844994+00:00
-- url     : https://prove2.me/submissions/1eddfc06-ba4e-4b2f-b26c-88b007a35a85

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.crePoly_hpsi
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_hermiteMv
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_add_single
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (α : Fin d →₀ ℕ) :
    crePoly i (hpsi α) = ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ) • hpsi (α + Finsupp.single i 1) := by

  have hne : ((hermiteMvNorm α : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero α
  have hne' : ((hermiteMvNorm (α + Finsupp.single i 1) : ℝ) : ℂ) ≠ 0 :=
    hermiteMvNorm_ne_zero _
  rw [hpsi, map_smul, crePoly_hermiteMv, hpsi, smul_smul]
  congr 1
  rw [hermiteMvNorm_add_single]
  have hs : (0 : ℝ) < Real.sqrt ((α i : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsc : ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hs
  push_cast
  field_simp
