-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys19_original_weighted_masked_B_residual_vanishes_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T19:29:11.811601+00:00
-- url     : https://prove2.me/submissions/d4314430-a22b-445d-a88a-d48faaca3c6e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ),
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range n,
        a i * (R (u i) - R (u (i + 1)))) = 0 := by
  filter_upwards [
    avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  ] with ω hzero
  intro u a n
  dsimp only
  apply Finset.sum_eq_zero
  intro i hi
  have hleft := hzero (u i)
  have hright := hzero (u (i + 1))
  rw [hleft, hright]
  ring
