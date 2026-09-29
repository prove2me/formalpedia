-- Prove2me | solution 1 for BookProof.HermiteProductBasis.crePoly_hermiteMvLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:58.286087+00:00
-- url     : https://prove2.me/submissions/e0b80fdd-bca2-43f8-8c0c-3c6f24bb5562

-- Generated from ChapterHermiteProductBasis.lean — solution of BookProof.HermiteProductBasis.crePoly_hermiteMvLp
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_hermiteMv
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_add_single
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteProductBasis








open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (crePoly i (hermiteMv a))
      = ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (a + Finsupp.single i 1) := by

  rw [crePoly_hermiteMv, pgLp_hermiteMv_eq (a + Finsupp.single i 1), smul_smul,
    hermiteMvNorm_add_single]
  congr 1
  have hne : ((hermiteMvNorm a : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero a
  push_cast
  field_simp
