-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_discounted_J_commutator_total_variation_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:26:40.038896+00:00
-- url     : https://prove2.me/submissions/3b699758-b902-4ebb-b1bc-f2c6dcdc3936

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_raw_negative_J_grid_total_variation_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Actual J-variation absorbs the discounted mixed X/J reserve commutator on every physical finite grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P,
      ∀ (u : ℕ → ℝ≥0) (n : ℕ),
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        let z : ℕ → ℝ := fun i =>
          x + X.X (u i) ω - rightLimit D (u i) ω
        let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
        let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
        (∀ i, i < n → u i ≤ u (i + 1)) →
        ∀ ε : ℝ, 0 ≤ ε →
        (∀ i, i < n →
          |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| ≤ ε * |j i|) →
        ∀ q : ℝ, 0 ≤ q →
          |∑ i ∈ Finset.range n,
            Real.exp (-q * (u i : ℝ)) *
              (w (z i + c i - j i) - w (z i + c i) -
                w (z i - j i) + w (z i))| ≤
          ε * (J (u n) - J (u 0)) := by
  filter_upwards
    [avram_p3_f2_original_raw_negative_J_grid_total_variation_exact X hBV]
    with ω hJ
  intro u n J Y z c j hGrid ε hε hCell q hq
  have hTerm (i : ℕ) (hi : i < n) :
      |Real.exp (-q * (u i : ℝ)) *
          (w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i))| ≤ ε * |j i| := by
    have hu : 0 ≤ (u i : ℝ) := by positivity
    have hWeight : Real.exp (-q * (u i : ℝ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) hu
    rw [abs_mul, abs_of_nonneg ((Real.exp_pos _).le)]
    calc
      Real.exp (-q * (u i : ℝ)) *
          |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| ≤
          1 * |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| :=
            mul_le_mul_of_nonneg_right hWeight (abs_nonneg _)
      _ = |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| := one_mul _
      _ ≤ ε * |j i| := hCell i hi
  calc
    |∑ i ∈ Finset.range n,
      Real.exp (-q * (u i : ℝ)) *
        (w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i))| ≤
      ∑ i ∈ Finset.range n,
        |Real.exp (-q * (u i : ℝ)) *
          (w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * |j i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact hTerm i (Finset.mem_range.mp hi)
    _ = ε * (J (u n) - J (u 0)) := by
      rw [← Finset.mul_sum]
      have hMass := hJ u n hGrid
      simpa only [j] using congrArg (fun s : ℝ => ε * s) hMass
