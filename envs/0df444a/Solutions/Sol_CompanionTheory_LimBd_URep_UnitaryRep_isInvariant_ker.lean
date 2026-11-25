-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.isInvariant_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:44.029219+00:00
-- url     : https://prove2.me/submissions/ae7e3585-4bc8-406a-8f50-b96f410cd15c

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
variable {π}
variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}
namespace CompanionTheory.LimBd.URep.UnitaryRep
theorem _root_.solution {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    π.IsInvariant (LinearMap.ker (T : H →ₗ[ℂ] K)) := by
  intro g v hv
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
  rw [hT, hv, map_zero]
end CompanionTheory.LimBd.URep.UnitaryRep
