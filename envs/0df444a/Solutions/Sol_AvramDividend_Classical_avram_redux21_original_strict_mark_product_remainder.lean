-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux21_original_strict_mark_product_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:39:20.548884+00:00
-- url     : https://prove2.me/submissions/7c5581dc-9069-490b-a199-593b4b3d2135

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_finite_mark_product_first_order_remainder
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let S : Finset ℝ≥0 :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let z : ℝ≥0 → ℝ := fun u =>
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    0 ≤ (∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u)) ∧
    2 * ((∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u))) ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
  classical
  let S : Finset ℝ≥0 :=
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let z : ℝ≥0 → ℝ := fun u =>
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  change 0 ≤ (∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u)) ∧
    2 * ((∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u))) ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1)
  apply avram_redux20_finite_mark_product_first_order_remainder S z
  intro u hu
  have hmem : u ∈ {v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
      X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v <
        -(1 / ((k : ℝ) + 1))} := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hu
  have hcut : -(1 / ((k : ℝ) + 1)) ≤ 0 :=
    neg_nonpos.mpr (by positivity)
  have hjump :
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 :=
    le_trans (le_of_lt hmem.2.2) hcut
  exact ⟨Real.exp_nonneg _,
    Real.exp_le_one_iff.mpr hjump⟩
