-- Prove2me | solution 1 for BookProof.QgHermiteOscillator.eq_zero_of_inner_basis_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:10:33.509494+00:00
-- url     : https://prove2.me/submissions/50ac004c-2d7d-456e-bcd4-68f9c18a2074

-- Generated from ChapterQgHermiteOscillatorEsa.lean — solution of BookProof.QgHermiteOscillator.eq_zero_of_inner_basis_eq_zero
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.QgHermiteOscillator












open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ι : Type*} {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ι ℂ F) {w : F}
    (h : ∀ i, (inner ℂ (b i) w : ℂ) = 0) : w = 0 := by

  have hrep : b.repr w = 0 := by
    ext i
    rw [b.repr_apply_apply]
    simpa using h i
  have := congrArg b.repr.symm hrep
  simpa using this
