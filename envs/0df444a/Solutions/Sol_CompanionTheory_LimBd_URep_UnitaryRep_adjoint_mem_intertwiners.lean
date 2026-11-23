-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.adjoint_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:34.146798+00:00
-- url     : https://prove2.me/submissions/6def6557-ec79-4437-95fd-47870dc3e336

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_inner_map_left
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_inner_map_right

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
    adjoint T ∈ σ.intertwiners π := by
  intro g w
  apply ext_inner_left ℂ
  intro v
  rw [adjoint_inner_right, inner_map_right π, adjoint_inner_right, hT, inner_map_left σ, inv_inv]
end CompanionTheory.LimBd.URep.UnitaryRep
