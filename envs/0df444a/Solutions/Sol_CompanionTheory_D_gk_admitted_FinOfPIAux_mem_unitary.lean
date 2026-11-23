-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:49.317276+00:00
-- url     : https://prove2.me/submissions/9e5f5ce1-89f3-43c5-906e-84e275e93651

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_star_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) :
    σ g ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff, star_eq σ hσ, ← map_mul, ← map_mul, inv_mul_cancel, mul_inv_cancel, map_one]
  exact ⟨rfl, rfl⟩
end CompanionTheory.D.gk.admitted.FinOfPIAux
