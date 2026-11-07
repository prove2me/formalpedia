-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:27:08.382007+00:00
-- url     : https://prove2.me/submissions/34ffeef1-b243-4409-85b2-58f3487410b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Variable-endpoint prefixes of the original BV source are dominated by
its fixed-horizon variation mass, by appending the final contact cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (k : ℕ),
      u 0 = 0 → u k ≤ T →
      (∀ i, i < k → u i ≤ u (i + 1)) →
      (let J : ℝ≥0 → ℝ := fun t =>
         ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
           Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       (∑ i ∈ Finset.range k, |Y (u (i + 1)) - Y (u i)|) ≤
         |X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|) := by
  filter_upwards
    [avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
      X hBV T] with ω hω
  dsimp at hω ⊢
  intro u k h0 hk hmono
  let v : ℕ → ℝ≥0 := fun i => if i ≤ k then u i else T
  have hv0 : v 0 = 0 := by simp [v, h0]
  have hvend : v (k + 1) = T := by simp [v]
  have hvmono : ∀ i, i < k + 1 → v i ≤ v (i + 1) := by
    intro i hi
    by_cases hik : i < k
    · have hil : i ≤ k := Nat.le_of_lt hik
      have his : i + 1 ≤ k := Nat.succ_le_of_lt hik
      simpa only [v, if_pos hil, if_pos his] using hmono i hik
    · have hieq : i = k := by omega
      subst i
      simpa [v] using hk
  have hFull := hω v (k + 1) hv0 hvend hvmono
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  have hsplit :
      (∑ i ∈ Finset.range (k + 1), |Y (v (i + 1)) - Y (v i)|) =
      (∑ i ∈ Finset.range k, |Y (u (i + 1)) - Y (u i)|) +
        |Y T - Y (u k)| := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      simp only [v, if_pos (Nat.le_of_lt hik),
        if_pos (Nat.succ_le_of_lt hik)]
    · simp [v]
  change (∑ i ∈ Finset.range (k + 1),
    |Y (v (i + 1)) - Y (v i)|) ≤ _ at hFull
  rw [hsplit] at hFull
  exact le_trans (le_add_of_nonneg_right (abs_nonneg _)) hFull
