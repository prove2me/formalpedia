-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.inner_map_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:41.503354+00:00
-- url     : https://prove2.me/submissions/2f9c4db1-a01b-4acd-a85d-cc74737d655c

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm

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
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
variable {G : Type} [Group G] {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : G →* (H →L[ℂ] H)} {σ' : G →* (H' →L[ℂ] H')}
omit [CompleteSpace H]
namespace CompanionTheory.D.gk.Poul
theorem _root_.solution (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (v w : H) : ⟪σ g v, w⟫_ℂ = ⟪v, σ g⁻¹ w⟫_ℂ := by
  have h := (⟨(σ g : H →ₗ[ℂ] H), hiso g⟩ : H →ₗᵢ[ℂ] H).inner_map_map v (σ g⁻¹ w)
  have e : σ g (σ g⁻¹ w) = w := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [← h]
  show _ = ⟪σ g v, σ g (σ g⁻¹ w)⟫_ℂ
  rw [e]
end CompanionTheory.D.gk.Poul
