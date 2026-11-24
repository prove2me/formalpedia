-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Weil.QuotInt.exists_fib_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:41.547051+00:00
-- url     : https://prove2.me/submissions/140fbce5-d44c-4080-b86e-ad2f48b23eb9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator
import Theorems.Thm_Formalism_L2_SG_Pf_Weil_QuotInt_measurable_fib
import Theorems.Thm_Formalism_L2_SG_Pf_Weil_QuotInt_fib_mul
import Theorems.Thm_Formalism_L2_SG_Pf_Weil_QuotInt_measure_coset_le
import Theorems.Thm_Formalism_L2_SG_Pf_Weil_QuotInt_measure_coset_lt_top
import Theorems.Thm_Formalism_L2_SG_Pf_Weil_QuotInt_measure_nhds_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Weil
open Formalism.L2.SG.Pf.Weil.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] {H : Subgroup G}
namespace Formalism.L2.SG.Pf.Weil.QuotInt
theorem _root_.solution (hH : IsClosed (H : Set G)) (κ : Measure H) [SFinite κ]
    [κ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts κ] [IsOpenPosMeasure κ] :
    ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ x, fib κ β x = 1 := by
  obtain ⟨φ, hφ, hpos, hfin⟩ : ∃ φ : G → ℝ≥0∞, Measurable φ ∧ (∀ x, 0 < fib κ φ x) ∧
      (∀ x, fib κ φ x < ∞) := by
    obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
    have hVm : MeasurableSet V := hVc.isClosed.measurableSet
    let d := TopologicalSpace.denseSeq G
    have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq G
    have hS : ∀ y : G, MeasurableSet {h : H | y * (h : G) ∈ V} := fun y =>
      hVm.preimage ((measurable_const_mul y).comp measurable_subtype_coe)
    have hfib : ∀ x, fib κ (fun x => ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * V.indicator 1 ((d n)⁻¹ * x)) x
        = ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (d n)⁻¹ * x * (h : G) ∈ V} := by
      intro x
      have hm1 : ∀ n, Measurable (fun h : H => V.indicator (1 : G → ℝ≥0∞) ((d n)⁻¹ * (x * (h : G)))) :=
        fun n => (measurable_one.indicator hVm).comp
          ((measurable_const_mul _).comp ((measurable_const_mul x).comp measurable_subtype_coe))
      have hm : ∀ n, Measurable (fun h : H =>
          (2⁻¹ : ℝ≥0∞) ^ n * V.indicator (1 : G → ℝ≥0∞) ((d n)⁻¹ * (x * (h : G)))) :=
        fun n => measurable_const.mul (hm1 n)
      show ∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * V.indicator (1 : G → ℝ≥0∞) ((d n)⁻¹ * (x * (h : G))) ∂κ = _
      rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
      congr 1
      funext n
      rw [lintegral_const_mul _ (hm1 n)]
      congr 1
      rw [← lintegral_indicator_one (hS ((d n)⁻¹ * x))]
      congr 1
      funext h
      simp only [Function.comp_apply, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, mul_assoc]
      first | rfl | simp [Set.indicator_apply]
    have hC : κ {h : H | (h : G) ∈ V⁻¹ * V} < ∞ := measure_coset_lt_top hH κ hVc
    refine ⟨fun x => ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * V.indicator 1 ((d n)⁻¹ * x), ?_, ?_, ?_⟩
    · exact Measurable.ennreal_tsum (fun n => measurable_const.mul
        ((measurable_one.indicator hVm).comp (measurable_const_mul _)))
    · intro x
      rw [hfib x]
      have hopen : IsOpen {g : G | g⁻¹ * x ∈ interior V} :=
        isOpen_interior.preimage (continuous_inv.mul continuous_const)
      obtain ⟨n, hn⟩ := hd.exists_mem_open hopen ⟨x, by simpa using mem_interior_iff_mem_nhds.2 hV1⟩
      have hn' : (d n)⁻¹ * x ∈ interior V := hn
      have hnb : {z : G | (d n)⁻¹ * x * z ∈ V} ∈ 𝓝 (1 : G) := by
        have hc : ContinuousAt (fun z : G => (d n)⁻¹ * x * z) 1 :=
          (continuous_const.mul continuous_id).continuousAt
        have hV' : V ∈ 𝓝 ((fun z : G => (d n)⁻¹ * x * z) 1) := by
          simpa using mem_interior_iff_mem_nhds.1 hn'
        exact hc.preimage_mem_nhds hV'
      have hpos' := measure_nhds_pos κ hnb
      calc (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (d n)⁻¹ * x * (h : G) ∈ V} :=
            ENNReal.mul_pos (by simp) hpos'.ne'
        _ ≤ _ := ENNReal.le_tsum n
    · intro x
      rw [hfib x]
      have hle : ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (d n)⁻¹ * x * (h : G) ∈ V}
          ≤ ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (h : G) ∈ V⁻¹ * V} := by
        have hn : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (d n)⁻¹ * x * (h : G) ∈ V}
            ≤ (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (h : G) ∈ V⁻¹ * V} := by
          intro n
          first
          | exact mul_le_mul_of_nonneg_left (measure_coset_le κ _ V) (by simp)
          | exact mul_le_mul_left (measure_coset_le κ _ V) _
        first
        | exact ENNReal.tsum_le_tsum hn
        | exact tsum_le_tsum hn ENNReal.summable ENNReal.summable
        | exact Summable.tsum_le_tsum hn ENNReal.summable ENNReal.summable
      refine lt_of_le_of_lt hle ?_
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      first
      | exact ENNReal.mul_lt_top (by simp) hC
      | exact ENNReal.mul_lt_top (by simp) hC.ne
  refine ⟨fun x => φ x * (fib κ φ x)⁻¹, ?_, ?_⟩
  · first
    | exact hφ.mul (measurable_fib κ hφ).inv
    | exact hφ.mul (ENNReal.continuous_inv.measurable.comp (measurable_fib κ hφ))
  · intro x
    have e : ∀ h : H, φ (x * h) * (fib κ φ (x * h))⁻¹ = φ (x * h) * (fib κ φ x)⁻¹ := fun h => by
      rw [fib_mul]
    show ∫⁻ h, φ (x * h) * (fib κ φ (x * h))⁻¹ ∂κ = 1
    simp_rw [e]
    have hφx : Measurable (fun h : H => φ (x * (h : G))) :=
      hφ.comp ((measurable_const_mul x).comp measurable_subtype_coe)
    rw [lintegral_mul_const _ hφx]
    exact ENNReal.mul_inv_cancel (hpos x).ne' (hfin x).ne
end Formalism.L2.SG.Pf.Weil.QuotInt
