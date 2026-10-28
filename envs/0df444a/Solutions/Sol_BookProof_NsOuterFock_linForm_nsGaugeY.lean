-- Prove2me | solution 1 for BookProof.NsOuterFock.linForm_nsGaugeY
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-27T05:56:05.079572+00:00
-- url     : https://prove2.me/submissions/23190c67-990a-468d-8733-648d1a24df7b

-- Generated from ChapterNsOuterFockFarisLavine.lean — solution of BookProof.NsOuterFock.linForm_nsGaugeY
import Mathlib
import Definitions.Def_ChapterNsOuterFockFarisLavine
import Theorems.Thm_BookProof_NsOuterFock_linForm_nsVec
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.NsOuterFock




open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL
open BookProof.SqSumOuterFamily
open BookProof.QgOuterFock

noncomputable section

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (p : Fin n) (j : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locY j))
      = ((gg : ℝ) : ℂ) • X (coordOf p (locY j)) := by

  rw [linForm_nsVec bv nu lam mu gg p (locY j) hne]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, sameVec, nextVec, locY,
    Fin.sum_univ_three]
  fin_cases j <;> simp
