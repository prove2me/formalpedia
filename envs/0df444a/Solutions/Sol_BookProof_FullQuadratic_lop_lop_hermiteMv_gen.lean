-- Prove2me | solution 1 for BookProof.FullQuadratic.lop_lop_hermiteMv_gen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:57:20.142304+00:00
-- url     : https://prove2.me/submissions/d5fe615c-fe3f-4550-a22f-6a0a8dbf13e8

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.lop_lop_hermiteMv_gen
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Theorems.Thm_BookProof_FullQuadratic_add_pvec_eq
import Theorems.Thm_BookProof_FullQuadratic_sub_pvec_eq
import Theorems.Thm_BookProof_FullQuadratic_add_sub_single_eq_shiftm
import Theorems.Thm_BookProof_FullQuadratic_add_single_apply_ne
import Theorems.Thm_BookProof_FullQuadratic_smul_shiftm_diag
import Theorems.Thm_BookProof_ModeQuadratic_lop_hermiteMv
import Definitions.Def_ChapterHermiteProductBasis
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
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (t t' : ℂ) (i j : Fin d) (a : Fin d →₀ ℕ) :
    lop t i (lop t' j (hermiteMv a))
      = hermiteMv (a + pvec i j)
        + (t * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (t' * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + (t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
            • hermiteMv (a - pvec i j)
        + (if i = j then t • hermiteMv a else 0) := by

  rw [lop_hermiteMv t' j a, map_add, map_smul, lop_hermiteMv t i (a + Finsupp.single j 1),
    lop_hermiteMv t i (a - Finsupp.single j 1), add_pvec_eq, sub_pvec_eq]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, add_tsub_cancel_right]
    have hs : a - Finsupp.single i 1 + Finsupp.single i 1 = shiftm a i i := rfl
    rw [hs]
    have hd : ((a + Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) = a i + 1 := by simp
    rw [hd]
    rw [smul_shiftm_diag t a i]
    push_cast
    module
  · rw [if_neg hij, add_sub_single_eq_shiftm hij, add_single_apply_ne hij]
    have hs : a - Finsupp.single j 1 + Finsupp.single i 1 = shiftm a i j := rfl
    rw [hs]
    push_cast
    module
