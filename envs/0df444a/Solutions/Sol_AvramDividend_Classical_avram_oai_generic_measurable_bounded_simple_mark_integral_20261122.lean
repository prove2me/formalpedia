-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_generic_measurable_bounded_simple_mark_integral_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:27:36.607876+00:00
-- url     : https://prove2.me/submissions/a017d809-77f9-489f-b0d4-3975ca61d47d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_real_simple_mark_integral_partition_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure (ℝ≥0 × ℝ)) (hM : Measurable M)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hMass : ∀ᵐ ω ∂P, M ω (Ioc 0 T ×ˢ B) < ⊤)
    (f : SimpleFunc ℝ ℝ)
    (hBound : ∀ z ∈ B, |f z| ≤ 1) :
    AEStronglyMeasurable
      (fun ω => ∫ p in (Ioc 0 T ×ˢ B), f p.2 ∂M ω) P  := by
  let G : Ω → ℝ := fun ω =>
    ∑ y ∈ f.range, y * (M ω (Ioc 0 T ×ˢ (B ∩ f ⁻¹' {y}))).toReal
  have hG : Measurable G := by
    dsimp [G]
    apply Finset.measurable_sum
    intro y hy
    have hS : MeasurableSet (Ioc 0 T ×ˢ (B ∩ f ⁻¹' {y})) := by
      exact measurableSet_Ioc.prod (hB.inter ((measurableSet_singleton y).preimage f.measurable))
    have hmass : Measurable (fun ω => M ω (Ioc 0 T ×ˢ (B ∩ f ⁻¹' {y}))) :=
      (Measure.measurable_coe hS).comp hM
    exact measurable_const.mul (ENNReal.measurable_toReal.comp hmass)
  have hEq : (fun ω => ∫ p in (Ioc 0 T ×ˢ B), f p.2 ∂M ω) =ᵐ[P] G := by
    filter_upwards [hMass] with ω hm
    have hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => f p.2)
        (Ioc 0 T ×ˢ B) (M ω) := by
      exact (avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
        (M ω) T B hB (fun z => f z) f.measurable hm hBound).1
    exact avram_a20_real_simple_mark_integral_partition_exact
      (M ω) T B hB f hInt
  exact hG.aestronglyMeasurable.congr hEq.symm
