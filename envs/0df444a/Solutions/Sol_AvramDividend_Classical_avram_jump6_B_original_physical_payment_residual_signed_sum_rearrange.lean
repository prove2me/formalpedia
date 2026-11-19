-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_physical_payment_residual_signed_sum_rearrange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:24:30.489582+00:00
-- url     : https://prove2.me/submissions/3cc7a4cd-cd68-4f1d-81c9-b95ee7918243

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_weighted_signed_potential_drop_sum_swap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let E : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ)))
    let Y : ℝ≥0 → ℝ := fun r => x + X.X r ω - rightLimit D r ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range ((n + 1) * (j + 1)),
        E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) =
    (w (x - rightLimit D 0 ω) - w x) -
      (∑ i ∈ Finset.range ((n + 1) * (j + 1)),
        E (v (i + 1)) * (w (Z i) - w (Y (v (i + 1))))) := by
  intro v E Y Z
  rw [avram_jump6_B_weighted_signed_potential_drop_sum_swap]
  ring
