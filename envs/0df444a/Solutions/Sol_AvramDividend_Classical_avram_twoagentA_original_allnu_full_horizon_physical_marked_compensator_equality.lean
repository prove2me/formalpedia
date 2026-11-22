-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_allnu_full_horizon_physical_marked_compensator_equality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:05:30.637025+00:00
-- url     : https://prove2.me/submissions/df338361-3362-4510-bf61-bd364f19fc7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_Levy_complete_physical_marked_clock_factory
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_intrinsic_negative_jump_occupation_equals_physical_levy_product_of_future_rectangles
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ∞ ∧
      (∀ E : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] E →
        μ E = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E) ∧
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
      fun ω => @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    let MK : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
      P.bind K
    let N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        μ.prod (X.ν.restrict (Iio (0 : ℝ))))
    (MK.restrict {p | p.1.1 ≤ T}) = N := by
  obtain ⟨μ, hμ, hμclock, B, hBm, hBfin, hBmono, hBcover,
      hLocal, hFuture⟩ :=
    avram_pj_workerC_actual_Levy_complete_physical_marked_clock_factory X T
  refine ⟨μ, hμ, hμclock, ?_⟩
  exact
    avram_wave6_04_true_source_intrinsic_negative_jump_occupation_equals_physical_levy_product_of_future_rectangles
      X _ rfl T _ rfl _ _ rfl μ hμ hμclock rfl
      B hBm hBmono hBcover hLocal
      (fun i A C hA hC => hFuture i A hA C hC)

