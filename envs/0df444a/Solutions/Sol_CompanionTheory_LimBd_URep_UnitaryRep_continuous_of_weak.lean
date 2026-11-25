-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.continuous_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:16.053829+00:00
-- url     : https://prove2.me/submissions/af303181-3ba1-4e99-b534-d338e77be1f1

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
open CompanionTheory.LimBd.URep.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H)
namespace CompanionTheory.LimBd.URep.UnitaryRep
theorem _root_.solution (ρ : G →* unitary (H →L[ℂ] H))
    (hρ : ∀ v w : H, Continuous fun g => ⟪(ρ g : H →L[ℂ] H) v, w⟫_ℂ) (v : H) :
    Continuous fun g => (ρ g : H →L[ℂ] H) v := by
  rw [continuous_iff_continuousAt]
  intro h
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set w := (ρ h : H →L[ℂ] H) v
  have hsq : ∀ g, ‖(ρ g : H →L[ℂ] H) v - w‖ =
      Real.sqrt (2 * ‖v‖ ^ 2 - 2 * RCLike.re ⟪(ρ g : H →L[ℂ] H) v, w⟫_ℂ) := by
    intro g
    rw [← Real.sqrt_sq (norm_nonneg _), @norm_sub_sq ℂ, Unitary.norm_map, Unitary.norm_map]
    congr 1
    ring
  have hc : Continuous fun g =>
      Real.sqrt (2 * ‖v‖ ^ 2 - 2 * RCLike.re ⟪(ρ g : H →L[ℂ] H) v, w⟫_ℂ) :=
    (continuous_const.sub (continuous_const.mul (RCLike.continuous_re.comp (hρ v w)))).sqrt
  have h0 : Real.sqrt (2 * ‖v‖ ^ 2 - 2 * RCLike.re ⟪(ρ h : H →L[ℂ] H) v, w⟫_ℂ) = 0 := by
    rw [← hsq, sub_self, norm_zero]
  simp_rw [hsq]
  rw [← h0]
  exact hc.continuousAt
end CompanionTheory.LimBd.URep.UnitaryRep
