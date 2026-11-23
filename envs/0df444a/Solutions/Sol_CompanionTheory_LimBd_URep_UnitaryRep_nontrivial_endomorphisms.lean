-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.nontrivial_endomorphisms
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:39.960631+00:00
-- url     : https://prove2.me/submissions/c75c4601-ec59-4d7f-a249-33efd8093cac

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



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
omit [CompleteSpace H]
namespace CompanionTheory.LimBd.URep.UnitaryRep
theorem _root_.solution [Nontrivial H] : Nontrivial (H →L[ℂ] H) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  exact ⟨⟨1, 0, fun h => hv (by simpa using congrArg (fun T : H →L[ℂ] H => T v) h)⟩⟩
end CompanionTheory.LimBd.URep.UnitaryRep
