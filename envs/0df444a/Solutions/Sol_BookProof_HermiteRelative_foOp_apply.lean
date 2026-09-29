-- Prove2me | solution 1 for BookProof.HermiteRelative.foOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:52.163145+00:00
-- url     : https://prove2.me/submissions/d080a0ec-b329-4f4d-9f9e-f41c4a8b7cf5

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.foOp_apply
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_coreOp_add
import Theorems.Thm_BookProof_HermiteRelative_coreOp_smul
import Theorems.Thm_BookProof_HermiteRelative_coreOp_sum
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
open BookProof.HermiteRelative










open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive
theorem solution (b b' : Fin d → ℝ) (u : polyGaussCore (d := d)) :
    foOp b b' u = ∑ i, (((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u) := by

  simp only [foOp, foPoly, LinearMap.comp_apply, Submodule.subtype_apply, coreOp_sum,
    coreOp_add, coreOp_smul, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_add, Submodule.coe_smul]
  rfl
