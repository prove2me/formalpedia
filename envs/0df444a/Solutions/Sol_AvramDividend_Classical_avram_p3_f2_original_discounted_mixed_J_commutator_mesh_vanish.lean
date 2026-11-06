-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_discounted_mixed_J_commutator_mesh_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:28:01.790519+00:00
-- url     : https://prove2.me/submissions/401d4159-cd3e-43e7-995a-2da5b7570026

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_raw_negative_J_grid_total_variation_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Source-negative-J total variation makes the original discounted Y/J commutator vanish on refining physical grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let z : ℕ → ℕ → ℝ := fun m i =>
          x + X.X (u m i) ω - rightLimit D (u m i) ω
        let c : ℕ → ℕ → ℝ := fun m i =>
          Y (u m (i + 1)) - Y (u m i)
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
            |w (z m i + c m i - j m i) - w (z m i + c m i) -
              w (z m i - j m i) + w (z m i)| ≤ ε * |j m i|) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |∑ i ∈ Finset.range (n m),
              Real.exp (-q * (u m i : ℝ)) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))| < η := by
  filter_upwards
    [avram_p3_f2_original_raw_negative_J_grid_total_variation_exact X hBV]
    with ω hJ
  intro J Y T u n z c j hStart hEnd hGrid hCellEventually η hη
  let M : ℝ := J T - J 0
  let B : ℝ := |M| + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg M]
  have hε : 0 < η / B := div_pos hη hB
  filter_upwards [hCellEventually (η / B) hε] with m hCell
  have hMass := hJ (u m) (n m) (hGrid m)
  have hClock : J (u m (n m)) - J (u m 0) = M := by
    simp only [hStart m, hEnd m]
    rfl
  have hTerm (i : ℕ) (hi : i < n m) :
      |Real.exp (-q * (u m i : ℝ)) *
          (w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i))| ≤
          (η / B) * |j m i| := by
    have hu : 0 ≤ (u m i : ℝ) := by positivity
    have hWeight : Real.exp (-q * (u m i : ℝ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) hu
    rw [abs_mul, abs_of_nonneg ((Real.exp_pos _).le)]
    calc
      Real.exp (-q * (u m i : ℝ)) *
          |w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i)| ≤
          1 * |w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i)| :=
            mul_le_mul_of_nonneg_right hWeight (abs_nonneg _)
      _ = |w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i)| := one_mul _
      _ ≤ η / B * |j m i| := hCell i hi
  have hEstimate :
      |∑ i ∈ Finset.range (n m),
        Real.exp (-q * (u m i : ℝ)) *
          (w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i))| ≤ (η / B) * M := by
    calc
      |∑ i ∈ Finset.range (n m),
        Real.exp (-q * (u m i : ℝ)) *
          (w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i))| ≤
          ∑ i ∈ Finset.range (n m),
            |Real.exp (-q * (u m i : ℝ)) *
              (w (z m i + c m i - j m i) - w (z m i + c m i) -
                w (z m i - j m i) + w (z m i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (n m), (η / B) * |j m i| := by
        apply Finset.sum_le_sum
        intro i hi
        exact hTerm i (Finset.mem_range.mp hi)
      _ = (η / B) * M := by
        rw [← Finset.mul_sum]
        rw [← hClock]
        simpa only [j] using
          congrArg (fun s : ℝ => (η / B) * s) hMass
  have hMB : M < B := by
    dsimp [B]
    linarith [le_abs_self M]
  calc
    |∑ i ∈ Finset.range (n m),
      Real.exp (-q * (u m i : ℝ)) *
        (w (z m i + c m i - j m i) - w (z m i + c m i) -
          w (z m i - j m i) + w (z m i))| ≤ (η / B) * M := hEstimate
    _ < (η / B) * B := mul_lt_mul_of_pos_left hMB hε
    _ = η := by field_simp [ne_of_gt hB]
