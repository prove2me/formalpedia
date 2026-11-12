-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b22_original_postruin_closed_mark_uniform_floor_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:44:41.152447+00:00
-- url     : https://prove2.me/submissions/ddc5eadf-6807-4f0c-874b-292f620e0695

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual post-ruin physical closed-cap floor kernel eventually vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q T : ℝ)
    (hT : 0 < T) (ω : Ω) (t : ℝ≥0)
    (hpost : ruinTime X x D ω < (t : ℝ≥0∞)) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    Tendsto (fun n =>
      if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then
        Real.exp (-(q * (s n : ℝ))) *
          ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν
      else 0) atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
    (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
  let U : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
  have hfalse : ∀ᶠ n in atTop,
      ¬ ((s n : ℝ≥0∞) < ruinTime X x D ω) := by
    simpa only [s] using
      (avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
        T hT t (ruinTime X x D ω) hpost)
  have heq : (fun n =>
      if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then
        Real.exp (-(q * (s n : ℝ))) *
          ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν
      else 0) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [hfalse] with n hn
    simp [hn]
  exact (tendsto_congr' heq).2 tendsto_const_nhds
