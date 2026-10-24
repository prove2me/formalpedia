-- Prove2me | solution 1 for AvramDividend.Classical.negative_initial_reserve_killed_scale_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:47:57.962917+00:00
-- url     : https://prove2.me/submissions/dad80a46-c181-4ddf-a2d9-d535c78b3e2e

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : x < 0) (q : ℝ) (W : ℝ → ℝ) :
    Martingale
      (fun t ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}.indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω))
      𝓕 P := by
  have heq :
      (fun t : ℝ≥0 => fun ω : Ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}.indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω)) =
      (0 : ℝ≥0 → Ω → ℝ) := by
    funext t ω
    have hnot : ω ∉ {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} := by
      intro hsurv
      have hzero : 0 ≤ x + X.X (0 : ℝ≥0) ω :=
        hsurv (0 : ℝ≥0) (by positivity)
      simp only [X.X_zero ω, add_zero] at hzero
      exact (not_le_of_gt hx) hzero
    simp only [Set.indicator_of_notMem hnot, Pi.zero_apply]
  rw [heq]
  exact martingale_zero ℝ 𝓕 P
