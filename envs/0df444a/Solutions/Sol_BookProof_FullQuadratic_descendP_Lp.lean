-- Prove2me | solution 1 for BookProof.FullQuadratic.descendP_Lp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:59:25.756203+00:00
-- url     : https://prove2.me/submissions/8d26a64a-1b4e-420a-a169-bee8a615be3a

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.descendP_Lp
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Theorems.Thm_BookProof_FullQuadratic_pvec_comm
import Theorems.Thm_BookProof_FullQuadratic_sub_pvec_eq
import Theorems.Thm_BookProof_FullQuadratic_swap_prodC
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_sub_single
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
open BookProof.FullQuadratic




open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.CarlemanSimplex
open BookProof.ModeQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ •
        ((c * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
          • pgLp (hermiteMv (a - pvec i j)))
      = (c * ((lcp a i j : ℝ) : ℂ)) • hermiteMvLp (a - pvec i j) := by

  have hco : c * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)
      = c * (a i : ℂ) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ) := by
    rw [mul_assoc, mul_assoc, swap_prodC]
  rw [hco]
  rcases Nat.eq_zero_or_pos (a i) with h0 | hposi
  · have hlcp : lcp a i j = 0 := by rw [lcp, h0]; simp
    rw [hlcp, h0]
    simp
  · rcases Nat.eq_zero_or_pos ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j) with h0 | hposj
    · have hlcp : lcp a i j = 0 := by rw [lcp, h0]; simp
      rw [hlcp, h0]
      simp
    · have hn1 : hermiteMvNorm a
          = hermiteMvNorm (a - Finsupp.single i 1) * Real.sqrt ((a i : ℝ)) :=
        hermiteMvNorm_sub_single hposi
      have hn2 : hermiteMvNorm (a - Finsupp.single i 1)
          = hermiteMvNorm (a - Finsupp.single i 1 - Finsupp.single j 1)
              * Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ)) :=
        hermiteMvNorm_sub_single hposj
      have hsub : a - Finsupp.single i 1 - Finsupp.single j 1 = a - pvec i j := by
        rw [sub_pvec_eq a j i, pvec_comm]
      have hsi : Real.sqrt ((a i : ℝ)) * Real.sqrt ((a i : ℝ)) = (a i : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hsj : Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ))
            * Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ))
          = (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hsine : ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        have : (0 : ℝ) < Real.sqrt ((a i : ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast hposi)
        linarith
      have hsjne : ((Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ)) : ℝ) : ℂ)
          ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        have : (0 : ℝ) < Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ)) :=
          Real.sqrt_pos.mpr (by exact_mod_cast hposj)
        linarith
      have hbne : ((hermiteMvNorm (a - pvec i j) : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero _
      rw [hsub] at hn2
      rw [pgLp_hermiteMv_eq, smul_smul, smul_smul, lcp, hn1, hn2]
      congr 1
      set m : ℕ := a i with hm
      set n : ℕ := ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) with hn
      have hc1 : ((m : ℂ)) = ((Real.sqrt ((m : ℝ)) : ℝ) : ℂ) * ((Real.sqrt ((m : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hsi]
        simp
      have hc2 : ((n : ℂ)) = ((Real.sqrt ((n : ℝ)) : ℝ) : ℂ) * ((Real.sqrt ((n : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hsj]
        simp
      push_cast
      field_simp
      rw [hc1, hc2]
      ring
