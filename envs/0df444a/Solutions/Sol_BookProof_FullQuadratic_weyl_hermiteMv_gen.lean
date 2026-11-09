-- Prove2me | solution 1 for BookProof.FullQuadratic.weyl_hermiteMv_gen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:57:27.795581+00:00
-- url     : https://prove2.me/submissions/9ff174d6-c73f-4456-8f95-960e49687db1

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.weyl_hermiteMv_gen
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Theorems.Thm_BookProof_FullQuadratic_pvec_comm
import Theorems.Thm_BookProof_FullQuadratic_swap_prodC
import Theorems.Thm_BookProof_FullQuadratic_lop_lop_hermiteMv_gen
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
import Definitions.Def_ChapterYangMillsHermite
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
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (t t' : ℂ) (i j : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (lop t i) (lop t' j) (hermiteMv a)
      = hermiteMv (a + pvec i j)
        + (t * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (t' * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + (t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
            • hermiteMv (a - pvec i j)
        + (if i = j then ((t + t') / 2) • hermiteMv a else 0) := by

  rw [BookProof.YangMillsHermite.weylProd]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
  have hco : t' * t * (a i : ℂ) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ)
      = t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ) := by
    have hsw := swap_prodC a i j
    calc t' * t * (a i : ℂ) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ)
        = (t' * t) * ((a i : ℂ) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ)) := by
          ring
      _ = (t * t') * ((a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) := by
          rw [← hsw]; ring
      _ = t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ) := by ring
  rw [lop_lop_hermiteMv_gen t t' i j a, lop_lop_hermiteMv_gen t' t j i a,
    ← pvec_comm j i, hco]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    push_cast
    module
  · rw [if_neg hij, if_neg (Ne.symm hij), if_neg hij]
    push_cast
    module
