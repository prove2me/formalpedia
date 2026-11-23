-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.contDiff_hs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:36.862858+00:00
-- url     : https://prove2.me/submissions/1497be59-5b80-4a72-81c9-bd7bac6346f8

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
theorem _root_.solution : ContDiff ℝ ∞ (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (contDiff_entry i j).norm_sq ℝ
end CompanionTheory.D.gk.admitted.Gard
