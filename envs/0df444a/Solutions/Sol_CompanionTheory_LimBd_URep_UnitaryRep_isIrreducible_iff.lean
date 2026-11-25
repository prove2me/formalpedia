-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.isIrreducible_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:57.947876+00:00
-- url     : https://prove2.me/submissions/c5782d0a-c859-47ee-b37f-d9b6c0d9fe54

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsIrreducible_exists_eq_smul_one
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_isInvariant_iff_commute_starProjection
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_mem_intertwiners_self_iff
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
namespace CompanionTheory.LimBd.URep.UnitaryRep
theorem _root_.solution :
    π.IsIrreducible ↔
      Nontrivial H ∧ ∀ T ∈ π.intertwiners π, ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  refine ⟨fun hπ => ⟨hπ.1, fun T hT => hπ.exists_eq_smul_one hT⟩, fun ⟨hnt, h⟩ => ⟨hnt, ?_⟩⟩
  intro V hcl hinv
  have : CompleteSpace V := hcl.completeSpace_coe
  have hP : V.starProjection ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun g => ((isInvariant_iff_commute_starProjection V).mp hinv g).symm
  obtain ⟨c, hc⟩ := h _ hP
  have hPv : ∀ v, V.starProjection v = c • v := fun v => by simp [hc]
  by_cases hc0 : c = 0
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot, ← Submodule.starProjection_eq_self_iff.mpr hv, hPv, hc0, zero_smul]
  · right
    rw [eq_top_iff]
    intro v _
    have hmem : V.starProjection v ∈ V := V.starProjection_apply_mem v
    rw [hPv] at hmem
    simpa [hc0] using V.smul_mem c⁻¹ hmem
end CompanionTheory.LimBd.URep.UnitaryRep
