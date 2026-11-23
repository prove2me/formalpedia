-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:41.17497+00:00
-- url     : https://prove2.me/submissions/680b8b60-7621-421b-99c5-934efb861fa8

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
variable (π) (V : Submodule ℂ H) [CompleteSpace V] (hV : π.IsInvariant V)
namespace CompanionTheory.LimBd.URep.UnitaryRep
theorem _root_.solution (g : G) (v : V) :
    ((π.restrict V hV g v : V) : H) = π g v := rfl
end CompanionTheory.LimBd.URep.UnitaryRep
