-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_stopped_bounded_physical_cell_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:35:44.185095+00:00
-- url     : https://prove2.me/submissions/4d53552f-a79f-49f4-8e09-2045eb072fe4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    MemLp (fun ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)
        then (0 : ℝ) else H ω) * ((N ω).toReal-r)) 2 P := by
  classical
  let W : Ω → ℝ := fun ω =>
    if (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)
    then (0 : ℝ) else H ω
  have hs : MeasurableSet[𝓕.rightCont s]
      {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)} :=
    hτstop s
  have hWsm : StronglyMeasurable[𝓕.rightCont s] W :=
    StronglyMeasurable.ite hs stronglyMeasurable_const hH
  have hWbound : ∀ ω, |W ω| ≤ L := by
    intro ω
    by_cases h : (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)
    · simpa only [W, if_pos h, abs_zero] using
        (abs_nonneg (H ω)).trans (hBound ω)
    · simpa only [W, if_neg h] using hBound ω
  exact avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
    X s T cut W hWsm L hWbound
