-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genX_genX_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:11.784381+00:00
-- url     : https://prove2.me/submissions/75202ad1-2aa6-41ad-8e12-f6404bc017a2

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genX_genX_commute
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_swap
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow


@[simp] private theorem genX_apply (j : Fin 3) (p : NSAlg) : genX j p = pderiv (NSVar.x j) p := rfl

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 3) : ⁅genX j, genX k⁆ = 0 := by

  refine LinearMap.ext fun p => ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply,
    genX_apply, pderiv_swap (NSVar.x j) (NSVar.x k)]
  ring
