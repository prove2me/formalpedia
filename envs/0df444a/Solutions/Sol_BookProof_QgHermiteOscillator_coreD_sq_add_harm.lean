-- Prove2me | solution 1 for BookProof.QgHermiteOscillator.coreD_sq_add_harm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:10:32.367255+00:00
-- url     : https://prove2.me/submissions/b1c71f4e-64b3-4bba-b7db-aa51cf5bc389

-- Generated from ChapterQgHermiteOscillatorEsa.lean — solution of BookProof.QgHermiteOscillator.coreD_sq_add_harm
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Theorems.Thm_BookProof_HermiteProductBasis_annPoly_apply
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_apply
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
theorem solution (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    -coreD j (coreD j p) + C (1 / 4 : ℂ) * (X j ^ 2 * p)
      = crePoly j (annPoly j p) + C (1 / 2 : ℂ) * p := by

  have hC2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  have h14 : (C (1 / 4 : ℂ) : MvPolynomial (Fin d) ℂ) = C (1 / 2 : ℂ) * C (1 / 2 : ℂ) := by
    rw [← C_mul]; norm_num
  simp only [coreD, map_sub, pderiv_mul, pderiv_C, pderiv_X_self, crePoly_apply, annPoly_apply,
    h14]
  linear_combination (X j * pderiv j p) * hC2
