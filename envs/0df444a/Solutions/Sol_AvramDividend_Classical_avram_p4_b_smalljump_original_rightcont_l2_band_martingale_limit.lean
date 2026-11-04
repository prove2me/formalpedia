-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_rightcont_l2_band_martingale_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:38:27.464285+00:00
-- url     : https://prove2.me/submissions/db01a5be-9396-4672-859a-b0de66dc4664

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_filtration_l2_band_martingale_limit
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- L2 limits of the original right-continuous source finite-band martingales
remain martingales, with the trimmed probability sigma-finiteness supplied by
the genuine original filtration. The finite-band hypotheses remain explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (L : ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (hconv : ∀ t, Tendsto (fun n => M n t) atTop (𝓝 (L t)))
    (hAdapt : ∀ s n,
      ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (M n s) :
        Lp ℝ (2 : ℝ≥0∞) P) = M n s)
    (hCenter : ∀ s t, s ≤ t → ∀ n,
      (MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (M n t - M n s) = 0) :
    (∀ s, ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (L s) :
      Lp ℝ (2 : ℝ≥0∞) P) = L s) ∧
    (∀ s t, s ≤ t →
      ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (L t) :
        Lp ℝ (2 : ℝ≥0∞) P) = L s) := by
  exact avram_wave5_02b_original_filtration_l2_band_martingale_limit
    P (𝓕.rightCont)
    (avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite 𝓕)
    M L hconv hAdapt hCenter
