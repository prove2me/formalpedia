-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.hamCore_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:23:45.828036+00:00
-- url     : https://prove2.me/submissions/79b5c46b-952a-4e4a-8f76-e6db96fb4051

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.hamCore_symmetricOn
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_pgLp
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_kinPoly
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_kinPoly_left
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_pgLp
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_potLp_symm
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hWc : Continuous W) (hWb : ExpBounded W) :
    SymmetricOn (polyGaussCore (d := d)) (hamCore W hWc hWb) := by

  intro x y
  obtain ⟨p, hp⟩ := x.2
  obtain ⟨q, hq⟩ := y.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  have hy : y = ⟨pgLp q, pgLp_mem_core q⟩ := Subtype.ext hq.symm
  rw [hx, hy, hamCore_pgLp, hamCore_pgLp]
  change (inner ℂ (hamPoly W hWc hWb p) (pgLp q) : ℂ) = inner ℂ (pgLp p) (hamPoly W hWc hWb q)
  simp only [hamPoly, inner_add_left, inner_add_right]
  congr 1
  · rw [inner_pgLp_pgLp, inner_pgLp_pgLp, gaussInt_kinPoly_left, gaussInt_kinPoly]
  · exact inner_potLp_symm W hWc hWb p q
