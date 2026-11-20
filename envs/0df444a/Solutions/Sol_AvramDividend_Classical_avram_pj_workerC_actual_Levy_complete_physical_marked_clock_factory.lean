-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_Levy_complete_physical_marked_clock_factory
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:22:09.887066+00:00
-- url     : https://prove2.me/submissions/69505dd8-98de-442e-9f41-a4db1f8bf731

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_Levy_finite_predictable_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_full_mark_bands_future_local_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ∞ ∧
      (∀ E : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] E →
        μ E = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) E) ∧
      (
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
    ∃ B : ℕ → Set ℝ,
      (∀ n, MeasurableSet (B n)) ∧
      (∀ n, (X.ν.restrict (Iio (0 : ℝ))) (B n) < ∞) ∧
      Monotone B ∧ (⋃ n, B n) = Set.univ ∧
      (∀ n, (MK.restrict {p | p.1.1 ≤ T})
        ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B n) ≠ ∞) ∧
      (∀ (i : ℝ≥0) (A : Set Ω),
        MeasurableSet[𝓕.rightCont i] A → ∀ C : Set ℝ,
        MeasurableSet C →
        (MK.restrict {p | p.1.1 ≤ T}) ((Ioi i ×ˢ A) ×ˢ C) =
          N ((Ioi i ×ˢ A) ×ˢ C))) := by
  obtain ⟨μ, hμfinite, hμclock⟩ :=
    avram_pj_workerC_true_Levy_finite_predictable_physical_clock X T
  refine ⟨μ, hμfinite, hμclock, ?_⟩
  exact
    avram_pj_workerC_actual_full_mark_bands_future_local_source
      X T μ hμclock hμfinite
