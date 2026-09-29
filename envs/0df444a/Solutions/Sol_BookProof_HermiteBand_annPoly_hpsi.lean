-- Prove2me | solution 1 for BookProof.HermiteBand.annPoly_hpsi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:04:59.650355+00:00
-- url     : https://prove2.me/submissions/ea122ac7-e8ef-426d-ab93-47d968d0bebd

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.annPoly_hpsi
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteProductBasis_annPoly_apply
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_sub_single
import Theorems.Thm_BookProof_HermiteProductBasis_pderiv_hermiteMv
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (α : Fin d →₀ ℕ) :
    annPoly i (hpsi α) = ((Real.sqrt (α i : ℝ) : ℝ) : ℂ) • hpsi (α - Finsupp.single i 1) := by

  have hne : ((hermiteMvNorm α : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero α
  rw [hpsi, map_smul, annPoly_apply, pderiv_hermiteMv, hpsi, smul_smul, smul_smul]
  rcases Nat.eq_zero_or_pos (α i) with h0 | hpos
  · rw [h0]; simp
  · congr 1
    have hnorm := hermiteMvNorm_sub_single (i := i) (a := α) hpos
    have hsub_pos := hermiteMvNorm_pos (α - Finsupp.single i 1)
    have hai : (0 : ℝ) < (α i : ℝ) := by exact_mod_cast hpos
    have hsqrt : Real.sqrt ((α i : ℝ)) * Real.sqrt ((α i : ℝ)) = (α i : ℝ) :=
      Real.mul_self_sqrt hai.le
    have hsqrt_pos : 0 < Real.sqrt ((α i : ℝ)) := Real.sqrt_pos.mpr hai
    have hreal : (hermiteMvNorm α)⁻¹ * (α i : ℝ)
        = Real.sqrt ((α i : ℝ)) * (hermiteMvNorm (α - Finsupp.single i 1))⁻¹ := by
      rw [hnorm]
      field_simp
      nlinarith [hsqrt, hsub_pos, hsqrt_pos]
    have := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hreal
    push_cast at this ⊢
    linear_combination this
