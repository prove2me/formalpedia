-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_drift_mixed_commutator_J_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:19:43.196895+00:00
-- url     : https://prove2.me/submissions/e4199cf6-2396-4cf1-8d16-d97ef6bce617

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_raw_negative_J_grid_total_variation_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every original finite BV jump-variation telescope controls
any discounted mixed commutator, including pure physical drift cells,
from a uniform local epsilon-times-jump bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      (∀ i : ℕ, i < n → u i ≤ u (i + 1)) →
      ∀ (z c : ℕ → ℝ) (ε : ℝ), 0 ≤ ε →
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∀ i : ℕ, i < n →
        |w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i)| ≤ ε * |j i|) →
      |∑ i ∈ Finset.range n,
        Real.exp (-(q * (u i : ℝ))) * (w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i))| ≤
      ε * (J (u n) - J (u 0)) := by
  have hVariation :=
    avram_p3_f2_original_raw_negative_J_grid_total_variation_exact X hBV
  filter_upwards [hVariation] with ω hω
  intro u n hGrid z c ε hε J j hCell
  have hVar : (∑ i ∈ Finset.range n, |j i|) = J (u n) - J (u 0) := by
    simpa only [J, j] using hω u n hGrid
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |Real.exp (-(q * (u i : ℝ))) *
          (w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * |j i| := by
      apply Finset.sum_le_sum
      intro i hi
      have hNonpos : -(q * (u i : ℝ)) ≤ 0 := by
        exact neg_nonpos.mpr (mul_nonneg hq (NNReal.coe_nonneg _))
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-(q * (u i : ℝ))) * |w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i)| ≤
          1 * |w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i)| := by
            exact mul_le_mul_of_nonneg_right
              (Real.exp_le_one_iff.mpr hNonpos) (abs_nonneg _)
        _ = |w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i)| := one_mul _
        _ ≤ ε * |j i| := hCell i (Finset.mem_range.mp hi)
    _ = ε * (J (u n) - J (u 0)) := by
      rw [← Finset.mul_sum, hVar]
