-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_masked_physical_generator_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:01:40.044948+00:00
-- url     : https://prove2.me/submissions/8d00776f-24a2-4fb4-aba3-01058403ee75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, u n i ≤ u n (i + 1))
    (Z : ℕ → ℕ → Ω → ℝ) (clock : ℕ → ℕ → Ω → Prop)
    (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range (n + 1),
      if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z n i ω) - q * w (Z n i ω)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with hmask
  · rcases hmask with ⟨hclock, hpos, hcap⟩
    have hGen := (hw (Z n i ω) hpos hcap).2
    have hExp : 0 ≤ Real.exp (-(q * (u n i : ℝ))) :=
      (Real.exp_pos _).le
    have hTime : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hu n i)
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hExp hGen) hTime
  · norm_num
