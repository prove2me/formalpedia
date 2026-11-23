-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.integral_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:40.13979+00:00
-- url     : https://prove2.me/submissions/b341f4ce-0dad-45b4-93f8-5d73440e9963

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
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
theorem _root_.solution {π : UnitaryRep G H} (hπ : SqInt μ π) {v : H} (hv : v ≠ 0) :
    0 < ∫ g, ‖⟪v, π g v⟫_ℂ‖ ^ 2 ∂μ := by
  have hc : Continuous fun g => ‖⟪v, π g v⟫_ℂ‖ ^ 2 :=
    ((continuous_const.inner (π.continuous_orbit v)).norm).pow 2
  have hi : Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ 2) μ := (hπ v v).norm.integrable_sq
  rw [integral_pos_iff_support_of_nonneg (fun g => by positivity) hi]
  refine hc.isOpen_support.measure_pos μ ⟨1, ?_⟩
  simp [hv]
end CompanionTheory.LimBd.URep
