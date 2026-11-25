-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.map_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:20.653025+00:00
-- url     : https://prove2.me/submissions/8bc3b716-0d4d-4f5c-bb07-2b1b4c2f0cb9

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
theorem _root_.solution (g : G) : Function.Injective (π g) := fun v w h => by
  have := congrArg (π g⁻¹) h
  rwa [map_inv_apply_map, map_inv_apply_map] at this
end CompanionTheory.LimBd.URep.UnitaryRep
