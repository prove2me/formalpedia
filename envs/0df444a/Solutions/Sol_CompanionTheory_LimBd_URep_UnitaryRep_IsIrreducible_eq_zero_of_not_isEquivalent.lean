-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.IsIrreducible.eq_zero_of_not_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:43.697147+00:00
-- url     : https://prove2.me/submissions/d113c1cc-cbf3-42aa-ac23-475aae3d91d6

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsIrreducible_isEquivalent_of_mem_intertwiners

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open CompanionTheory.LimBd.URep.UnitaryRep
open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}
namespace CompanionTheory.LimBd.URep.UnitaryRep
namespace IsIrreducible
theorem _root_.solution (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hne : ¬ π.IsEquivalent σ) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) : T = 0 := by
  by_contra h
  exact hne (hπ.isEquivalent_of_mem_intertwiners hσ hT h)
end IsIrreducible
end CompanionTheory.LimBd.URep.UnitaryRep
