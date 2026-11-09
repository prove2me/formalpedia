-- Prove2me | solution 1 for BookProof.FullQuadratic.fqTerm_hermiteMv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:57:46.926256+00:00
-- url     : https://prove2.me/submissions/5f3bacb1-563f-4df7-8e29-2d775e97252d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.fqTerm_hermiteMv
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Theorems.Thm_BookProof_FullQuadratic_weyl_hermiteMv_gen
import Theorems.Thm_BookProof_FullQuadratic_momsq_gen
import Theorems.Thm_BookProof_FullQuadratic_xsq_gen
import Theorems.Thm_BookProof_FullQuadratic_weylxp_gen
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
theorem solution (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) (a : Fin d →₀ ℕ) :
    (((P i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly j)
      + ((Q i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j)
      + ((S i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly j))
        (hermiteMv a)
      = fqAmp P Q S i j • hermiteMv (a + pvec i j)
        + ((starRingEnd ℂ) (fqMl P Q S i j) * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (fqMl P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + ((starRingEnd ℂ) (fqAmp P Q S i j) * (a j : ℂ)
            * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) • hermiteMv (a - pvec i j)
        + (if i = j then (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a else 0) := by

  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [momsq_gen, xsq_gen, weylxp_gen,
    weyl_hermiteMv_gen (-1) (-1) i j a, weyl_hermiteMv_gen 1 1 i j a,
    weyl_hermiteMv_gen 1 (-1) i j a, fqAmp, fqMl]
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    push_cast
    module
  · simp only [if_neg hij, add_zero]
    push_cast
    module
