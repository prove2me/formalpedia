-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.sqSumOp_pgLp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:55:18.228609+00:00
-- url     : https://prove2.me/submissions/77f155bd-9e96-440a-91bf-d3b69e266bbf

-- probe draft; generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.sqSumOp_pgLp
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.QgOuterFock
open BookProof.SqSumFarisLavine

variable {D : ℕ} {R : Type*} [Fintype R]



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

set_option autoImplicit false

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 BookProof.QgOuterFock in
theorem solution {D : ℕ} {R : Type*} [Fintype R] (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    sqSumOp kappa v ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (BookProof.SqSumFarisLavine.sqSumPoly kappa v p) := by
  have h : (BookProof.NavierStokesFlow.DifferentialL2.coreEquiv (d := D)).symm
      ⟨pgLp p, pgLp_mem_core p⟩ = p := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [sqSumOp, LinearMap.comp_apply, Submodule.subtype_apply,
    BookProof.NavierStokesFlow.DifferentialL2.coreOp, LinearEquiv.coe_coe, h]
  rfl
