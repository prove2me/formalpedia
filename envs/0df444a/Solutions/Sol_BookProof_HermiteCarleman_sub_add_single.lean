-- Prove2me | solution 1 for BookProof.HermiteCarleman.sub_add_single
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:27:01.852733+00:00
-- url     : https://prove2.me/submissions/e570d433-0119-4b75-91dc-15542fe3cfaa

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
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

theorem solution {d : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} (h : a i ≠ 0) :
    (a - Finsupp.single i 1) + Finsupp.single i 1 = a := by
  ext j
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [Finsupp.single_apply, Ne.symm hj]
