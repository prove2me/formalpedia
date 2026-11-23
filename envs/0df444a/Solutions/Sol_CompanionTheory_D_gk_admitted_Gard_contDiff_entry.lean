-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.contDiff_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:42.800323+00:00
-- url     : https://prove2.me/submissions/007d89bd-650e-4339-8fa6-d7d6ffb3dc2f

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump

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
theorem _root_.solution (i j : Fin n) : ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => y i j :=
  contDiff_apply_apply ℝ ℂ i j
end CompanionTheory.D.gk.admitted.Gard
