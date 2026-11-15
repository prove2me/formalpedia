-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB55_original_rational_caplinear_cutoff_HJB_and_positive_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:19:42.010614+00:00
-- url     : https://prove2.me/submissions/008618e2-414b-4526-8798-a9f212d62c9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_finitecap_rational_clip_strict_interior
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) :
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    0 ≤ w b ∧ ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0 := by
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  change 0 ≤ w b ∧ ∀ y : ℝ, 0 < y → y < b →
    X.generator w y - q * w y ≤ 0
  have hb :=
    avram_gbB41_original_finitecap_rational_clip_strict_interior
      C hC hFiniteCap j
  constructor
  · exact (avram_mix_fin26_original_reward_nonnegative_below_interior
      C hC w hw0 hw_cont hw_neg hw_smooth hw_grad
      b hb.1 hb.2 b le_rfl)
  · intro y hy hyb
    have hyC : ENNReal.ofReal y < C :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_of_lt hyb)) hb.2
    exact (hw_gen y hy hyC).2
