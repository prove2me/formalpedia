-- Prove2me | solution 1 for BookProof.QgHermiteOscillator.kinPoly_add_harmPoly_hermiteMv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:55:18.16007+00:00
-- url     : https://prove2.me/submissions/47e95933-ac78-427a-8e57-2347531a55ff

-- Generated from ChapterQgHermiteOscillatorEsa.lean — solution of BookProof.QgHermiteOscillator.kinPoly_add_harmPoly_hermiteMv
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Theorems.Thm_BookProof_QgHermiteOscillator_kinPoly_add_harmPoly
import Theorems.Thm_BookProof_QgHermiteOscillator_crePoly_annPoly_hermiteMv
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





variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin d →₀ ℕ) :
    kinPoly (hermiteMv a) + harmPoly * hermiteMv a
      = (((mvDeg a : ℂ) + (d : ℂ) / 2)) • hermiteMv a := by

  rw [kinPoly_add_harmPoly]
  simp only [crePoly_annPoly_hermiteMv]
  rw [← Finset.sum_smul]
  have hdeg : (∑ i : Fin d, ((a i : ℂ))) = (mvDeg a : ℂ) := by
    unfold mvDeg
    push_cast
    rfl
  rw [hdeg, add_smul]
  congr 1
  exact (MvPolynomial.smul_eq_C_mul _ _).symm
