-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.pairing_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:36.743245+00:00
-- url     : https://prove2.me/submissions/919c25c3-658e-41c1-8246-682cd2718386

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Theorems.Thm_CompanionTheory_LimBd_URep_exists_op_left
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsIrreducible_eq_zero_of_not_isEquivalent
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
noncomputable section
set_option linter.unusedSectionVars false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace CompanionTheory.LimBd.URep
theorem _root_.solution {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπi : π.IsIrreducible)
    (hσi : σ.IsIrreducible) (hπ : SqInt μ π) (hσ : SqInt μ σ) (hne : ¬ π.IsEquivalent σ)
    (v w : H) (v' w' : K) : pairing μ π σ v w v' w' = 0 := by
  obtain ⟨A, hA, h⟩ := exists_op_left hπ hσ v v'
  rw [h, hπi.eq_zero_of_not_isEquivalent hσi hne hA]
  simp
end CompanionTheory.LimBd.URep
