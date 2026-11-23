-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.exists_pairing_op
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:26.652035+00:00
-- url     : https://prove2.me/submissions/8d5e3ac8-8f3e-493a-9c72-d96aafb62c73

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Theorems.Thm_CompanionTheory_LimBd_URep_exists_to_L2
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
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace CompanionTheory.LimBd.URep
theorem _root_.solution (Φ : X → (H →L[ℂ] ℂ)) (hΦ : ∀ v, MemLp (fun x => Φ x v) 2 μ)
    (Ψ : X → (K →L[ℂ] ℂ)) (hΨ : ∀ v, MemLp (fun x => Ψ x v) 2 μ) :
    ∃ A : H →L[ℂ] K, ∀ v v', ∫ x, Φ x v * star (Ψ x v') ∂μ = ⟪v', A v⟫_ℂ := by
  obtain ⟨T, hT⟩ := exists_to_L2 Φ hΦ
  obtain ⟨S, hS⟩ := exists_to_L2 Ψ hΨ
  refine ⟨(ContinuousLinearMap.adjoint S).comp T, fun v v' => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hT v, hS v'] with x h1 h2
  rw [h1, h2]
  simp
end CompanionTheory.LimBd.URep
