-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_rightcont_l2_martingale_of_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:11:29.980826+00:00
-- url     : https://prove2.me/submissions/b0ff9016-bd7a-4064-9581-e6f575650dab

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightcont_l2_band_martingale_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (hCauchy : ∀ t, CauchySeq (fun n => M n t))
    (hAdapt : ∀ s n,
      ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (M n s) :
        Lp ℝ (2 : ℝ≥0∞) P) = M n s)
    (hCenter : ∀ s t, s ≤ t → ∀ n,
      (MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (M n t - M n s) = 0) :
    ∃ L : ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P,
      (∀ t, Tendsto (fun n => M n t) atTop (𝓝 (L t))) ∧
      (∀ s, ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (L s) :
        Lp ℝ (2 : ℝ≥0∞) P) = L s) ∧
      (∀ s t, s ≤ t →
        ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (L t) :
          Lp ℝ (2 : ℝ≥0∞) P) = L s) := by
  classical
  have hex : ∀ t, ∃ v : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto (fun n => M n t) atTop (𝓝 v) := by
    intro t
    exact cauchySeq_tendsto_of_complete (hCauchy t)
  choose L hconv using hex
  obtain ⟨ha, hm⟩ :=
    avram_p4_b_smalljump_original_rightcont_l2_band_martingale_limit
      P 𝓕 M L hconv hAdapt hCenter
  exact ⟨L, hconv, ha, hm⟩
