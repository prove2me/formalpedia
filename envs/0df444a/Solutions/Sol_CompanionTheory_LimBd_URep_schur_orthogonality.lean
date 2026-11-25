-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.schur_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:04.541831+00:00
-- url     : https://prove2.me/submissions/3be7ce3d-4c80-4a06-ac17-0cdca3c1b7ff

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Theorems.Thm_CompanionTheory_LimBd_URep_pairing_self
import Theorems.Thm_CompanionTheory_LimBd_URep_integral_sq_pos
import Theorems.Thm_CompanionTheory_LimBd_URep_exists_op_left
import Theorems.Thm_P2M_CompanionTheory_LimBd_URep_exists_op_right__1dec45d5e274
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsIrreducible_exists_eq_smul_one
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
theorem _root_.solution {π : UnitaryRep G H} (hirr : π.IsIrreducible) (hπ : SqInt μ π) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H, pairing μ π π v w v' w' = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  have := hirr.1
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : H)
  let u : H := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀
  have hn : ‖u‖ = 1 := by
    simp [u, norm_smul, hu₀]
  have hu : u ≠ 0 := fun h => by simp [h] at hn
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hn]; simp
  set s := ∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ
  have hs : 0 < s := integral_sq_pos hπ hu
  have hL : ∀ v v', ∃ c : ℂ, ∀ w w', pairing μ π π v w v' w' = c * ⟪w, w'⟫_ℂ := by
    intro v v'
    obtain ⟨A, hA, h⟩ := exists_op_left hπ hπ v v'
    obtain ⟨c, rfl⟩ := hirr.exists_eq_smul_one hA
    exact ⟨conj c, fun w w' => by rw [h]; simp [mul_comm]⟩
  obtain ⟨A, hA, h⟩ := exists_op_right' hπ hπ u u
  obtain ⟨e, rfl⟩ := hirr.exists_eq_smul_one hA
  have he : ∀ v v', pairing μ π π v u v' u = e * ⟪v', v⟫_ℂ := fun v v' => by
    rw [h]; simp
  have hes : e = (s : ℂ) := by
    have := he u u
    rw [huu, mul_one, pairing_self] at this
    exact this.symm
  refine ⟨s⁻¹, inv_pos.2 hs, fun v w v' w' => ?_⟩
  obtain ⟨c, hc⟩ := hL v v'
  have hce : c = e * ⟪v', v⟫_ℂ := by rw [← he, hc, huu, mul_one]
  rw [hc, hce, hes]
  push_cast
  rw [div_inv_eq_mul]
  ring
end CompanionTheory.LimBd.URep
