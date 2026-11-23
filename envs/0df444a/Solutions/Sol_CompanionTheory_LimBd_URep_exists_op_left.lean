-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.exists_op_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:02.887261+00:00
-- url     : https://prove2.me/submissions/273cba49-db53-4c04-bc52-44c6bf60e3ab

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Theorems.Thm_CompanionTheory_LimBd_URep_exists_pairing_op
import Theorems.Thm_CompanionTheory_LimBd_URep_pairing_left
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
theorem _root_.solution {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπ : SqInt μ π) (hσ : SqInt μ σ)
    (v : H) (v' : K) : ∃ A ∈ π.intertwiners σ, ∀ w w', pairing μ π σ v w v' w' = ⟪A w, w'⟫_ℂ := by
  obtain ⟨A, hA⟩ := exists_pairing_op (μ := μ) (fun g => innerSL ℂ (π g v))
    (fun w => by simpa [Pi.star_def] using (hπ v w).star) (fun g => innerSL ℂ (σ g v'))
    (fun w => by simpa [Pi.star_def] using (hσ v' w).star)
  have key : ∀ w w', pairing μ π σ v w v' w' = ⟪A w, w'⟫_ℂ := by
    intro w w'
    rw [← inner_conj_symm, ← hA, ← integral_conj]
    unfold pairing
    congr 1
    funext g
    simp
  refine ⟨A, fun h w => ?_, key⟩
  refine ext_inner_right ℂ fun w' => ?_
  rw [UnitaryRep.inner_map_left, ← key, ← key, ← pairing_left π σ v w v' _ h]
  simp
end CompanionTheory.LimBd.URep
