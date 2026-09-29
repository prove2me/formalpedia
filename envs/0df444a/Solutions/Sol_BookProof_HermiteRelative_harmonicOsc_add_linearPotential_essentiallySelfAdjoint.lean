-- Prove2me | solution 1 for BookProof.HermiteRelative.harmonicOsc_add_linearPotential_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:44:59.576074+00:00
-- url     : https://prove2.me/submissions/d5203bc2-2562-44bf-a510-8ffc93251936

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.harmonicOsc_add_linearPotential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_quadOp_add_firstOrder_essentiallySelfAdjoint
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
theorem solution (b : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (quadOp (fun _ => (1 : ℝ)) + foOp b 0) := quadOp_add_firstOrder_essentiallySelfAdjoint _ (c0 := 1) one_pos (fun _ => le_rfl) b 0
