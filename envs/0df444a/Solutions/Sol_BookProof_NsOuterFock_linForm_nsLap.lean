-- Prove2me | solution 1 for BookProof.NsOuterFock.linForm_nsLap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-27T05:54:35.622185+00:00
-- url     : https://prove2.me/submissions/0721b26e-d8df-4e4e-85c7-3ed62ec6ca97

-- Generated from ChapterNsOuterFockFarisLavine.lean — solution of BookProof.NsOuterFock.linForm_nsLap
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
theorem solution {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locL i))
      = ((mu : ℝ) : ℂ) • (X (coordOf p (locL i)) + (∑ j : Fin 3, X (coordOf p (locD i j)))
          - ∑ j : Fin 3, X (coordOf (nextPart p) (locD i j))) := by

  rw [linForm_nsVec bv nu lam mu gg p (locL i) hne]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, sameVec, nextVec, locD, locL,
    Fin.sum_univ_three]
  fin_cases i <;> simp <;> module
