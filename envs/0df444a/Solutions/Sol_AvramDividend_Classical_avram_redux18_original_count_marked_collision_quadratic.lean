-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_original_count_marked_collision_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:23:36.1022+00:00
-- url     : https://prove2.me/submissions/496de57e-4bf4-4f9d-a7f5-3ecd8ca4893e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_mark_product_collision
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_collision_second_moment_quadratic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The original physical count's quadratic budget dominates marked collisions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    {α : Type*} [DecidableEq α] (S : Ω → Finset α)
    (q : Ω → α → ℝ)
    (hS : ∀ ω, (S ω).card ≤
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)
    (hq0 : ∀ ω i, 0 ≤ q ω i) (hq1 : ∀ ω i, q ω i ≤ 1)
    (hE : Integrable (fun ω =>
      (∏ i ∈ S ω, q ω i) - (1 - ∑ i ∈ S ω, (1 - q ω i))) P) :
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    0 ≤ ∫ ω, ((∏ i ∈ S ω, q ω i) -
      (1 - ∑ i ∈ S ω, (1 - q ω i))) ∂P ∧
    (∫ ω, ((∏ i ∈ S ω, q ω i) -
      (1 - ∑ i ∈ S ω, (1 - q ω i))) ∂P) ≤ r ^ 2 := by
  classical
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let E : Ω → ℝ := fun ω =>
    (∏ i ∈ S ω, q ω i) - (1 - ∑ i ∈ S ω, (1 - q ω i))
  let Q : Ω → ℝ := fun ω =>
    if 2 ≤ K ω then ((K ω : ℝ) ^ 2) else 0
  change 0 ≤ ∫ ω, E ω ∂P ∧ (∫ ω, E ω ∂P) ≤ r ^ 2
  change Integrable E P at hE
  have hSource :=
    AvramDividend.Classical.avram_p4_s3_original_negative_band_collision_second_moment_quadratic X T n
  change Integrable Q P ∧ (∫ ω, Q ω ∂P) ≤ 2 * r ^ 2 at hSource
  have hBound (ω : Ω) : 0 ≤ E ω ∧ 2 * E ω ≤ Q ω := by
    have hmark := AvramDividend.Classical.avram_redux18_finite_mark_product_collision
      (S ω) (q ω) (hq0 ω) (hq1 ω)
    change 0 ≤ E ω ∧
      2 * E ω ≤ ((S ω).card : ℝ) * (((S ω).card : ℝ) - 1) at hmark
    constructor
    · exact hmark.1
    · have hSω : (S ω).card ≤ K ω := hS ω
      by_cases hk : 2 ≤ K ω
      · simp only [Q, hk, if_true]
        have hmle : ((S ω).card : ℝ) ≤ (K ω : ℝ) := by
          exact_mod_cast hSω
        have hm0 : (0 : ℝ) ≤ (S ω).card := Nat.cast_nonneg _
        have hk0 : (0 : ℝ) ≤ K ω := Nat.cast_nonneg _
        have hprod :
            0 ≤ ((K ω : ℝ) - (S ω).card) *
              ((K ω : ℝ) + (S ω).card) :=
          mul_nonneg (sub_nonneg.mpr hmle) (add_nonneg hk0 hm0)
        nlinarith [hmark.2]
      · simp only [Q, hk, if_false]
        have hk1 : K ω ≤ 1 := by omega
        have hm1 : (S ω).card ≤ 1 := hSω.trans hk1
        have hmle : ((S ω).card : ℝ) ≤ 1 := by exact_mod_cast hm1
        have hm0 : (0 : ℝ) ≤ (S ω).card := Nat.cast_nonneg _
        have hpair :
            ((S ω).card : ℝ) * (((S ω).card : ℝ) - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hm0 (sub_nonpos.mpr hmle)
        linarith [hmark.2]
  constructor
  · exact integral_nonneg (fun ω => (hBound ω).1)
  · have hmono : 2 * (∫ ω, E ω ∂P) ≤ ∫ ω, Q ω ∂P := by
      rw [← integral_const_mul]
      exact integral_mono (hE.const_mul 2) hSource.1
        (fun ω => (hBound ω).2)
    nlinarith [hSource.2]
