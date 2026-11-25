-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.mul_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:13:24.343706+00:00
-- url     : https://prove2.me/submissions/a14b879e-631a-40ba-ad9f-ecf34fe944e4

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_comp_mem_intertwiners

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
theorem _root_.solution {S T : H →L[ℂ] H} (hS : S ∈ π.intertwiners π)
    (hT : T ∈ π.intertwiners π) : S * T ∈ π.intertwiners π := comp_mem_intertwiners hS hT
end CompanionTheory.LimBd.URep.UnitaryRep
