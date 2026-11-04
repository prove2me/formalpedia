-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_intensity_short_strip_L1_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:51:51.829893+00:00
-- url     : https://prove2.me/submissions/d785f61e-66f3-4740-b602-a42e9664c79d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal

/-- At finite mark intensity, the original intrinsic jump count
inside shrinking initial time strips vanishes in first moment on any
original-space event, even one in the right-continuous past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (r : ℕ → ℝ≥0) (B : Set ℝ)
    (A : Set Ω)
    (hr : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hFinite : X.ν B ≠ ⊤)
    (hRate : ∀ n,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (r n) ×ˢ B) ∂P) =
        (((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) :
    Tendsto (fun n => (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (r n) ×ˢ B) ∂P))
      atTop (𝓝 0) := by
  let J (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
      (Ioc s (r n) ×ˢ B)
  change Tendsto (fun n => ∫⁻ ω in A, J n ω ∂P) atTop (𝓝 0)
  have hCoe :
      Tendsto (fun n => ((r n - s : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) :=
    (ENNReal.continuous_coe.tendsto 0).comp hr
  have hRight :
      Tendsto (fun n => ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
        atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (ENNReal.Tendsto.mul_const hCoe (Or.inr hFinite))
  have hBound (n : ℕ) :
      (∫⁻ ω in A, J n ω ∂P) ≤
        ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    calc
      (∫⁻ ω in A, J n ω ∂P) ≤ ∫⁻ ω, J n ω ∂P := by
        simpa using (lintegral_mono_set (Set.subset_univ A) :
          (∫⁻ ω in A, J n ω ∂P) ≤
            (∫⁻ ω in Set.univ, J n ω ∂P))
      _ = ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B := hRate n
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hRight
    (fun n => (zero_le : (0 : ℝ≥0∞) ≤ (∫⁻ ω in A, J n ω ∂P)))
    hBound
