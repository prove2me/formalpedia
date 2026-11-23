-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.toM_inv_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:46.843197+00:00
-- url     : https://prove2.me/submissions/ad22b881-0698-4238-9c4c-2f08258d4924

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open CompanionTheory.D.gk.admitted.Gard
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution {k : UJ ε} (hk : toM k ∈ Matrix.unitaryGroup (Fin n) ℂ) : toM k⁻¹ = (toM k)ᴴ :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 hk)
end CompanionTheory.D.gk.admitted.Gard
