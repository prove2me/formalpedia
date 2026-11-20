-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_full_mark_bands_future_local_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:06:43.206069+00:00
-- url     : https://prove2.me/submissions/1583b485-a0fc-42ab-8299-fd191d9fde5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_source_future_of_P2
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P) E)
    (hμfinite : μ Set.univ < ∞) :
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
          N ((Ioi i ×ˢ A) ×ˢ C)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro NX K MK N
  obtain ⟨B, hBm, hBfinite, hBmono, hBcover⟩ :=
    avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands X
  have hFuture : ∀ (i : ℝ≥0) (A : Set Ω),
      MeasurableSet[𝓕.rightCont i] A → ∀ C : Set ℝ,
      MeasurableSet C →
      (MK.restrict {p | p.1.1 ≤ T}) ((Ioi i ×ˢ A) ×ˢ C) =
        N ((Ioi i ×ˢ A) ×ˢ C) := by
    intro i A hA C hC
    exact avram_p4_f_assembly_original_rightcont_source_future_of_P2
      X T NX (by intro ω; rfl) K (by intro ω; rfl)
      MK rfl μ hμclock N rfl i A hA C hC
  have hLocal : ∀ n, (MK.restrict {p | p.1.1 ≤ T})
      ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B n) ≠ ∞ := by
    intro n
    have hFuture' : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
        MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
        (MK.restrict {p | p.1.1 ≤ T}) ((Ioi i ×ˢ A) ×ˢ C') =
          N ((Ioi i ×ˢ A) ×ˢ C') := by
      intro i A C' hA hC'
      exact hFuture i A hA C' hC'
    exact avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
      X K (by intro ω; rfl) MK rfl T {p | p.1.1 ≤ T}
      (MK.restrict {p | p.1.1 ≤ T}) N rfl
      μ hμfinite hμclock rfl (B n) (hBm n) (hBfinite n) hFuture' 
  exact ⟨B, hBm, hBfinite, hBmono, hBcover, hLocal, hFuture⟩
