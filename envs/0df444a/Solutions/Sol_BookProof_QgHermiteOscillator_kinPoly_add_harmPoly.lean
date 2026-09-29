-- Prove2me | solution 1 for BookProof.QgHermiteOscillator.kinPoly_add_harmPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:12.101168+00:00
-- url     : https://prove2.me/submissions/f12f1289-6327-4255-8f45-4e396f86966f

-- Generated from ChapterQgHermiteOscillatorEsa.lean — solution of BookProof.QgHermiteOscillator.kinPoly_add_harmPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Theorems.Thm_BookProof_QgHermiteOscillator_coreD_sq_add_harm
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
theorem solution (p : MvPolynomial (Fin d) ℂ) :
    kinPoly p + harmPoly * p
      = (∑ j : Fin d, crePoly j (annPoly j p)) + C ((d : ℂ) / 2) * p := by

  have hsum : kinPoly p + harmPoly * p
      = ∑ j : Fin d, (-coreD j (coreD j p) + C (1 / 4 : ℂ) * (X j ^ 2 * p)) := by
    simp only [kinPoly, harmPoly, Finset.sum_mul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum]
  simp only [coreD_sq_add_harm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((d : MvPolynomial (Fin d) ℂ)) = C (d : ℂ) := by
    simp
  rw [this, ← mul_assoc, ← C_mul]
  congr 2
  ring
