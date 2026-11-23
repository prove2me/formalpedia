-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.exists_to_L2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:19.512803+00:00
-- url     : https://prove2.me/submissions/091cd401-1d72-4bb7-8203-6979f96b4ccf

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
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace CompanionTheory.LimBd.URep
theorem _root_.solution (Φ : X → (H →L[ℂ] ℂ)) (hΦ : ∀ v, MemLp (fun x => Φ x v) 2 μ) :
    ∃ T : H →L[ℂ] Lp ℂ 2 μ, ∀ v, (T v : X → ℂ) =ᵐ[μ] fun x => Φ x v := by
  let T₀ : H →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun v => (hΦ v).toLp _
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by simp)
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by simp) }
  have hT₀ : ∀ v, (T₀ v : X → ℂ) =ᵐ[μ] fun x => Φ x v := fun v => MemLp.coeFn_toLp (hΦ v)
  have hc : Continuous T₀ := by
    refine T₀.continuous_of_seq_closed_graph fun u x y hu hy => ?_
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
    have hall : ∀ᵐ a ∂μ, ∀ n, (T₀ (u n) : X → ℂ) a = Φ a (u n) := ae_all_iff.2 fun n => hT₀ (u n)
    refine Lp.ext ?_
    filter_upwards [hae, hall, hT₀ x] with a h1 h2 h3
    rw [h3]
    have h4 : Tendsto (fun i => Φ a (u (ns i))) atTop (𝓝 (Φ a x)) :=
      ((Φ a).continuous.tendsto x).comp (hu.comp hns.tendsto_atTop)
    refine tendsto_nhds_unique ?_ h4
    simpa only [Function.comp_apply, h2] using h1
  exact ⟨⟨T₀, hc⟩, hT₀⟩
end CompanionTheory.LimBd.URep
