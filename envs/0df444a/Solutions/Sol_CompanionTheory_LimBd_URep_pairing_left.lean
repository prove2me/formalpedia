-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.pairing_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:16.700217+00:00
-- url     : https://prove2.me/submissions/8be0f882-e47e-431e-8fcf-ba28c057bd2d

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_inner_map_left
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
theorem _root_.solution (π : UnitaryRep G H) (σ : UnitaryRep G K) (v w : H) (v' w' : K) (h : G) :
    pairing μ π σ v (π h w) v' (σ h w') = pairing μ π σ v w v' w' := by
  unfold pairing
  rw [← integral_mul_left_eq_self (μ := μ) (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) h⁻¹]
  simp only [UnitaryRep.map_mul_apply, UnitaryRep.inner_map_left]
end CompanionTheory.LimBd.URep
