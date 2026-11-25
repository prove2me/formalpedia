-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.continuous_inner_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:14.362185+00:00
-- url     : https://prove2.me/submissions/aabfe807-d4d1-4cdd-ba4a-a4d8ed0b5e77

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
theorem _root_.solution (v w : H) : Continuous fun g => ⟪π g v, w⟫_ℂ :=
  (π.continuous_orbit v).inner continuous_const
end CompanionTheory.LimBd.URep.UnitaryRep
