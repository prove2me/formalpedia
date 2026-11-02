-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_original_filtration_l2_band_martingale_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:35:33.528498+00:00
-- url     : https://prove2.me/submissions/dd23e47e-34f1-4f15-9a50-2568194f7197

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_l2_conditional_centering_closed_under_band_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (hSigma : ∀ s : ℝ≥0, @SigmaFinite Ω (𝓕 s) (P.trim (𝓕.le s)))
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (L : ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (hconv : ∀ t, Tendsto (fun n => M n t) atTop (𝓝 (L t)))
    (hAdapt : ∀ s n,
      ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (M n s) :
        Lp ℝ (2 : ℝ≥0∞) P) = M n s)
    (hCenter : ∀ s t, s ≤ t → ∀ n,
      (MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (M n t - M n s) = 0) :
    (∀ s, ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (L s) :
      Lp ℝ (2 : ℝ≥0∞) P) = L s) ∧
    (∀ s t, s ≤ t →
      ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (L t) :
        Lp ℝ (2 : ℝ≥0∞) P) = L s) := by
  have hAdaptL : ∀ s, ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (L s) :
      Lp ℝ (2 : ℝ≥0∞) P) = L s := by
    intro s
    have ha : Tendsto (fun n =>
        ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (M n s) :
          Lp ℝ (2 : ℝ≥0∞) P)) atTop
        (𝓝 (((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (L s) :
          Lp ℝ (2 : ℝ≥0∞) P))) :=
      ((continuous_subtype_val.comp
        (MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)).continuous).tendsto
          (L s)).comp (hconv s)
    have hb : Tendsto (fun n =>
        ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (M n s) :
          Lp ℝ (2 : ℝ≥0∞) P)) atTop (𝓝 (L s)) := by
      simpa only [hAdapt s] using hconv s
    exact tendsto_nhds_unique ha hb
  refine ⟨hAdaptL, ?_⟩
  intro s t hst
  letI := hSigma s
  have hz := AvramDividend.Classical.avram_wave4_p1_l2_conditional_centering_closed_under_band_limit
    P (𝓕 s) (𝓕.le s) (fun n => M n t - M n s) (L t - L s)
    ((hconv t).sub (hconv s)) (hCenter s t hst)
  have heq : (MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (L t) =
      (MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (L s) := by
    simpa only [map_sub, sub_eq_zero] using hz
  exact (congrArg Subtype.val heq).trans (hAdaptL s)
