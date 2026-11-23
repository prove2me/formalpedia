-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.IsInvariant.orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:56.415938+00:00
-- url     : https://prove2.me/submissions/5075acd2-b6d4-4ad1-8041-c49e2b389a09

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
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
namespace CompanionTheory.LimBd.URep.UnitaryRep
namespace IsInvariant
theorem _root_.solution {V : Submodule ℂ H} (hV : π.IsInvariant V) :
    π.IsInvariant Vᗮ := by
  intro g v hv w hw
  rw [inner_map_right]
  exact hv _ (hV _ _ hw)
end IsInvariant
end CompanionTheory.LimBd.URep.UnitaryRep
