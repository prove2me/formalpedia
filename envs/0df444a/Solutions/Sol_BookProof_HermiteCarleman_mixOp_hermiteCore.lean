-- Prove2me | solution 1 for BookProof.HermiteCarleman.mixOp_hermiteCore
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:42:19.300908+00:00
-- url     : https://prove2.me/submissions/88d72cfc-fcfd-406c-95c1-0249940a9bc1

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mixOp_hermiteCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_hermiteMvLp
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.HermiteRelative
open BookProof.HyperbolicQuadratic
open BookProof.HermiteCarleman



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ} {lam : (Fin d →₀ ℕ) → ℝ} {amp : Fin d → ℂ} {z : ℂ}
theorem solution (c b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    mixOp c b b' (hermiteCore a)
      = ((quadSymbol c a : ℝ) : ℂ) • hermiteMvLp a
        + ∑ i, ((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ))
                  • hermiteMvLp (a + Finsupp.single i 1)
                + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ))
                  • hermiteMvLp (a - Finsupp.single i 1)) := by
  have h : hermiteMvLp a ∈ polyGaussCore (d := d) := (hermiteCore_coe a) ▸ (hermiteCore a).2
  show quadOp c (hermiteCore a) + foOp b b' (hermiteCore a) = _
  rw [foOp_hermiteCore, ← hermiteCore_eq a h, BookProof.HyperbolicQuadratic.quadOp_hermiteMvLp c a h]
