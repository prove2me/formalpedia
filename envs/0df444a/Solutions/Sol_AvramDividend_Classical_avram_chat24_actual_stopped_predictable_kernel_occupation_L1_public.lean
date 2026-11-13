-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_actual_stopped_predictable_kernel_occupation_L1_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:13:38.0793+00:00
-- url     : https://prove2.me/submissions/effba409-f046-43ed-99ee-368d0eba9ba7

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_rightcont_predictable_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rightcont_stopped_future_rect
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_physical_clock_general_stopped_source_L1_compensation_finite_levy_bands
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) 𝓕.rightCont.predictable)
    (hμfinite : μ univ < ∞)
    (hμclock : ∀ A, MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace ℝ))] G)
    (hGi : Integrable G (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : ℝ≥0∞)))
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let Ξ : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable (inferInstance : MeasurableSpace ℝ)) :=
      fun ω => @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) inferInstance
        (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable (inferInstance : MeasurableSpace ℝ))
        (fun p => ((p.1, ω), p.2)) (NX ω)
    Measurable[(@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace ℝ))] H ∧ Integrable H (P.bind Ξ) := by
  classical
  intro NX Ξ
  letI : SigmaFinite X.ν := avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite X
  have hΞ : AEMeasurable Ξ P :=
    avram_wave5_02a_original_rightcont_predictable_kernel_measurable X Ξ (fun ω => rfl)
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let M : Measure ((ℝ≥0 × Ω) × ℝ) := P.bind Ξ
  let N : Measure ((ℝ≥0 × Ω) × ℝ) := μ.prod (X.ν.restrict (Iio (0 : ℝ)))
  let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
  have hS : MeasurableSet S :=
    avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable 𝓕 T
  have hsupport : S.indicator H = H := by
    funext p
    by_cases ht : p ∈ S
    · exact Set.indicator_of_mem (s := S) (a := p) ht H
    · have hstop : ¬ (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) := by
        intro hp
        exact ht ((ENNReal.coe_le_coe.mp hp).trans (hτBound p.1.2))
      rw [Set.indicator_of_notMem (s := S) (a := p) ht H]
      simp only [hH, if_neg hstop]
  have hcomp :=
    avram_wave5_03_actual_physical_clock_general_stopped_source_L1_compensation_finite_levy_bands
      X NX (fun ω => rfl) Ξ (fun ω => rfl) hΞ M rfl T S rfl hS
      (M.restrict S) N rfl μ hμfinite hμclock rfl
      (spanningSets (X.ν.restrict (Iio (0 : ℝ))))
      (measurableSet_spanningSets _) (monotone_spanningSets _)
      (iUnion_spanningSets _) (measure_spanningSets_lt_top _)
      (fun i E B hE hB => avram_p2_e_compensator_original_rightcont_stopped_future_rect
        X T NX (fun ω => rfl) Ξ (fun ω => rfl) M rfl μ hμclock N rfl i E hE B hB)
      (fun ω => (τ ω : ℝ≥0∞)) hτ G hGm hGi H hH hsupport
  refine ⟨hcomp.1, ?_⟩
  have hI : Integrable (S.indicator H) M := (integrable_indicator_iff hS).2 hcomp.2.1
  simpa only [hsupport] using hI
