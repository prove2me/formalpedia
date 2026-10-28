-- Prove2me | solution 1 for BookProof.HermiteCarleman.mixOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:42:28.330433+00:00
-- url     : https://prove2.me/submissions/58b80751-aa71-4e44-ad5a-17fcc5a47e7e

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mixOp_symmetric
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_symmetric
import Theorems.Thm_BookProof_HermiteRelative_foOp_symmetric
import Theorems.Thm_BookProof_KatoRellich_symmetricOn_add
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
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
theorem solution (c b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (mixOp c b b') := by
  exact BookProof.KatoRellich.symmetricOn_add (BookProof.HyperbolicQuadratic.quadOp_symmetric c) (BookProof.HermiteRelative.foOp_symmetric b b')
