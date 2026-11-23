-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.IsInvariant.topologicalClosure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:56.004909+00:00
-- url     : https://prove2.me/submissions/8e4c1adf-f83e-4c61-b81b-0ea63239894b

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
namespace CompanionTheory.LimBd.URep.UnitaryRep
namespace IsInvariant
theorem _root_.solution {V : Submodule ℂ H} (hV : π.IsInvariant V) :
    π.IsInvariant V.topologicalClosure := by
  intro g v hv
  have hsub : Set.MapsTo (π g) (V : Set H) (V.topologicalClosure : Set H) :=
    fun x hx => V.le_topologicalClosure (hV g x hx)
  have hv' : v ∈ closure (V : Set H) := by
    rwa [← Submodule.topologicalClosure_coe]
  have := hsub.closure (π g).continuous hv'
  rwa [V.isClosed_topologicalClosure.closure_eq] at this
end IsInvariant
end CompanionTheory.LimBd.URep.UnitaryRep
