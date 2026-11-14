-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB36_original_full_negative_mark_rate_DCT
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:47:04.600608+00:00
-- url     : https://prove2.me/submissions/0bf95c9f-1d46-42a1-8b07-058832fc820b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Restored source-exact HJB36 dominated convergence after earlier candidate was locally quarantined by an unrelated shared publication-refresh timeout. Pointwise continuity and the full negative Levy measure integrable dominating function remain identical. -/
/- Current-checker revalidated full unmasked negative Levy mark DCT source theorem, preserving the exact pinned source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c : ℝ)
    (y : ℕ → ℝ) (hy : Tendsto y atTop (𝓝 c))
    (hwc : ContinuousAt w c)
    (hwz : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ContinuousAt w (c + z))
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))))
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun z : ℝ => w (y n + z) - w (y n))
      (X.ν.restrict (Iio (0 : ℝ))))
    (hDom : ∀ n, ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖w (y n + z) - w (y n)‖ ≤ ‖g z‖) :
    Tendsto (fun n => ∫ z in Iio (0 : ℝ),
      w (y n + z) - w (y n) ∂X.ν) atTop
      (𝓝 (∫ z in Iio (0 : ℝ), w (c + z) - w c ∂X.ν)) := by
  have hPoint : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      Tendsto (fun n : ℕ => w (y n + z) - w (y n))
        atTop (𝓝 (w (c + z) - w c)) := by
    filter_upwards [hwz] with z hz
    have hShift : Tendsto (fun n : ℕ => y n + z)
        atTop (𝓝 (c + z)) := by
      simpa using hy.add (tendsto_const_nhds (x := z))
    exact (hz.tendsto.comp hShift).sub (hwc.tendsto.comp hy)
  exact tendsto_integral_of_dominated_convergence
    (fun z : ℝ => ‖g z‖) hMeas hg.norm hDom hPoint
