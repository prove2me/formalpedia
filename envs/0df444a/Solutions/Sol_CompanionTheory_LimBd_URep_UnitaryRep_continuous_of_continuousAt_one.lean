-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.continuous_of_continuousAt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:11.660883+00:00
-- url     : https://prove2.me/submissions/e0926577-6a60-4a36-a243-11a866aea39d

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
theorem _root_.solution [IsTopologicalGroup G] (ρ : G →* unitary (H →L[ℂ] H))
    (hρ : ∀ v : H, ContinuousAt (fun g => (ρ g : H →L[ℂ] H) v) 1) (v : H) :
    Continuous fun g => (ρ g : H →L[ℂ] H) v := by
  rw [continuous_iff_continuousAt]
  intro h
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ g, ‖(ρ g : H →L[ℂ] H) v - (ρ h : H →L[ℂ] H) v‖ =
      ‖(ρ (h⁻¹ * g) : H →L[ℂ] H) v - v‖ := by
    intro g
    have e : ρ g = ρ h * ρ (h⁻¹ * g) := by rw [← MonoidHom.map_mul, mul_inv_cancel_left]
    have : (ρ g : H →L[ℂ] H) v - (ρ h : H →L[ℂ] H) v =
        (ρ h : H →L[ℂ] H) ((ρ (h⁻¹ * g) : H →L[ℂ] H) v - v) := by
      rw [map_sub, e]
      rfl
    rw [this, Unitary.norm_map]
  simp_rw [key]
  have ht : Tendsto (fun g => h⁻¹ * g) (𝓝 h) (𝓝 1) := by
    have := (continuous_const_mul h⁻¹).tendsto h
    rwa [inv_mul_cancel] at this
  have h1 := Filter.Tendsto.comp (hρ v) ht
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1
  simpa [Function.comp_def] using h1
end CompanionTheory.LimBd.URep.UnitaryRep
