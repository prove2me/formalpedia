-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_fatou_eventual_grid_lintegral_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:45:38.06763+00:00
-- url     : https://prove2.me/submissions/1ec48de3-2de8-4356-ac2e-2866165b11b9

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-- Fatou transfers eventually exact measurable source grid counts to their limit mean. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : ℕ → Ω → ℝ≥0∞) (K : Ω → ℝ≥0∞)
    (hMeas : ∀ n, Measurable (G n))
    (hEventual : ∀ ω, ∀ᶠ n in atTop, G n ω = K ω) :
    (∫⁻ ω, K ω ∂μ) ≤
      Filter.liminf (fun n : ℕ => ∫⁻ ω, G n ω ∂μ) atTop := by
  have hlim (ω : Ω) :
      Filter.liminf (fun n : ℕ => G n ω) atTop = K ω := by
    calc
      Filter.liminf (fun n : ℕ => G n ω) atTop =
          Filter.liminf (fun _ : ℕ => K ω) atTop :=
        Filter.liminf_congr (hEventual ω)
      _ = K ω := Filter.liminf_const _
  have hFatou := MeasureTheory.lintegral_liminf_le
    (μ := μ) (f := G) (u := atTop) hMeas
  simpa only [hlim] using hFatou
