-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.Equiv.mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:08.69847+00:00
-- url     : https://prove2.me/submissions/0ad8b0d7-8cb6-49d7-957e-f128d54c1293

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
open CompanionTheory.LimBd.URep.UnitaryRep.Equiv
namespace CompanionTheory.LimBd.URep.UnitaryRep.Equiv
theorem _root_.solution (e : π.Equiv σ) :
    (e.toLinearIsometryEquiv : H →L[ℂ] K) ∈ π.intertwiners σ := e.map_apply'
end CompanionTheory.LimBd.URep.UnitaryRep.Equiv
