-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_first_uniform_positive_mask_generator_cell_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:09:25.773215+00:00
-- url     : https://prove2.me/submissions/2ef9e1e5-a298-4de5-92ff-86f5272f055b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva19_original_first_cell_discounted_gain_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (q : ℝ) (ω : Ω)
    (u : ℕ → ℕ → ℝ≥0)
    (hzero : ∀ n, u n 0 = 0)
    (hmesh : Tendsto (fun n => (u n 1 : ℝ)) atTop (𝓝 (0 : ℝ))) :
    let U : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t
    Tendsto (fun n =>
      Real.exp (-(q * (u n 0 : ℝ))) *
      (if (u n 0 : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < U (u n 0) ∧ ENNReal.ofReal (U (u n 0)) < C then
        X.generator w (U (u n 0)) - q * w (U (u n 0))
      else 0) *
      ((u n 1 : ℝ) - (u n 0 : ℝ)))
      atTop (𝓝 (0 : ℝ))  := by
  let U : ℝ≥0 → ℝ := fun t => Function.leftLim
    (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t
  let ψ : ℝ → ℝ := fun y =>
    if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < y ∧ ENNReal.ofReal y < C then
      X.generator w y - q * w y
    else 0
  have h :=
    avram_bva19_original_first_cell_discounted_gain_vanishes
      u hzero hmesh U q ψ
  simpa [hzero, ψ, U] using h
