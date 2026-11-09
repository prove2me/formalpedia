-- Prove2me | solution 1 for BookProof.ModeQuadratic.descend2_Lp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T14:02:34.663754+00:00
-- url     : https://prove2.me/submissions/92441c77-598c-46bd-b1c0-5bf3036456f2

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.descend2_Lp
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Theorems.Thm_BookProof_ModeQuadratic_sub_single_one_one
import Theorems.Thm_BookProof_CarlemanTwoStep_lc2_vanish
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_sub_single
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ModeQuadratic




open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ •
        ((c * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • pgLp (hermiteMv (a - Finsupp.single i 2)))
      = (c * ((lc2 a i : ℝ) : ℂ)) • hermiteMvLp (a - Finsupp.single i 2) := by

  rcases Nat.lt_or_ge (a i) 2 with hlt | hge
  · have hz : (a i : ℂ) * (((a i - 1 : ℕ) : ℂ)) = 0 := by
      interval_cases hai : (a i)
      · simp
      · simp
    have hlc : lc2 a i = 0 := lc2_vanish i a hlt
    rw [hlc]
    rw [show c * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ)) = c * ((a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) by
      ring, hz]
    simp
  · have hpos1 : 1 ≤ a i := by omega
    have hsub1 : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by simp
    have hpos2 : 1 ≤ (a - Finsupp.single i 1 : Fin d →₀ ℕ) i := by rw [hsub1]; omega
    have hn1 : hermiteMvNorm a
        = hermiteMvNorm (a - Finsupp.single i 1) * Real.sqrt ((a i : ℝ)) :=
      hermiteMvNorm_sub_single hpos1
    have hn2 : hermiteMvNorm (a - Finsupp.single i 1)
        = hermiteMvNorm (a - Finsupp.single i 2) * Real.sqrt (((a i - 1 : ℕ) : ℝ)) := by
      have h := hermiteMvNorm_sub_single (i := i) (a := a - Finsupp.single i 1) hpos2
      rw [sub_single_one_one, hsub1] at h
      exact h
    have hnorm : hermiteMvNorm a
        = hermiteMvNorm (a - Finsupp.single i 2)
            * (Real.sqrt (((a i - 1 : ℕ) : ℝ)) * Real.sqrt ((a i : ℝ))) := by
      rw [hn1, hn2]; ring
    have hlc : lc2 a i = Real.sqrt ((a i : ℝ)) * Real.sqrt (((a i - 1 : ℕ) : ℝ)) := by
      rw [lc2, ← Real.sqrt_mul (by positivity)]
      congr 1
      have : ((a i - 1 : ℕ) : ℝ) = (a i : ℝ) - 1 := by
        push_cast [Nat.cast_sub hpos1]
        ring
      rw [this]
    have hsq1 : Real.sqrt ((a i : ℝ)) * Real.sqrt ((a i : ℝ)) = (a i : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsq2 : Real.sqrt (((a i - 1 : ℕ) : ℝ)) * Real.sqrt (((a i - 1 : ℕ) : ℝ))
        = ((a i - 1 : ℕ) : ℝ) := Real.mul_self_sqrt (by positivity)
    rw [pgLp_hermiteMv_eq, smul_smul, smul_smul, hlc]
    congr 1
    have hne : ((hermiteMvNorm a : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero a
    have hnesub : ((hermiteMvNorm (a - Finsupp.single i 2) : ℝ) : ℂ) ≠ 0 :=
      hermiteMvNorm_ne_zero _
    have hs1 : ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      have : (0 : ℝ) < Real.sqrt ((a i : ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast hpos1)
      linarith
    have hs2 : ((Real.sqrt (((a i - 1 : ℕ) : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      have : (0 : ℝ) < Real.sqrt (((a i - 1 : ℕ) : ℝ)) :=
        Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < a i - 1))
      linarith
    rw [hnorm]
    push_cast
    field_simp
    have hc1 : ((a i : ℂ))
        = ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hsq1]; simp
    have hc2 : (((a i - 1 : ℕ) : ℂ))
        = ((Real.sqrt (((a i - 1 : ℕ) : ℝ)) : ℝ) : ℂ)
            * ((Real.sqrt (((a i - 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hsq2]; simp
    rw [hc1, hc2]
    ring
