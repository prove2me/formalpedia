-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.contDiff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:44.119847+00:00
-- url     : https://prove2.me/submissions/e65b323e-7ad6-48a1-9257-b2df604b8187

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2 := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => ((contDiff_entry i k).comp contDiff_fst).mul ((contDiff_entry k j).comp contDiff_snd)
end CompanionTheory.D.gk.admitted.Gard
