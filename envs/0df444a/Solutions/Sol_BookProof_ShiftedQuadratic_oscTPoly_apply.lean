-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.oscTPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:27:00.512131+00:00
-- url     : https://prove2.me/submissions/e3a840fc-777d-45e9-bbc2-0fbf984cc011

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.oscTPoly_apply
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}
theorem h44x_mulX {d : ℕ} (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    BookProof.NavierStokesFlow.DifferentialL2.mulXPoly i p = MvPolynomial.X i * p := rfl

theorem solution (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    oscTPoly a k i p = oscPoly i p + (2 * ((k i : ℝ) : ℂ)) • momPoly i p
      + (((a i : ℝ) : ℂ) / 2) • (X i * p)
      + ((((k i : ℝ) : ℂ)) ^ 2 + ((a i : ℝ) : ℂ) ^ 2 / 4) • p := by
  simp only [oscTPoly, momTPoly, mulXTPoly, oscPoly, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul]
  simp only [h44x_mulX]
  module

