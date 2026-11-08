-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn10_original_shortcell_product_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:07:06.539685+00:00
-- url     : https://prove2.me/submissions/037706d1-633c-405e-8cbe-daca0e398111

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_shortcell_original_marked_bochner_range
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_shortcell_original_mark_loss_real_mean
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_shortcell_original_marked_collision_expectation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Integrate the original marked product by separating its first moment and
    nonnegative finite-pair collision remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let q : ℝ := (∫ ω : Ω, ∏ u ∈
        (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset,
        Real.exp (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) ∂P)
    let a : ℝ := (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν)
    let C : ℝ := (X.ν (Iic (-(1 / ((k : ℝ) + 1))))).toReal ^ 2
    0 ≤ q ∧ q ≤ 1 ∧
    0 ≤ q - (1 - a / ((n + 1 : ℕ) : ℝ)) ∧
    q - (1 - a / ((n + 1 : ℕ) : ℝ)) ≤
      C / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let q : ℝ := ∫ ω, W ω ∂P
  let a : ℝ := ∫ y in Iio (-(1 / ((k : ℝ) + 1))),
    (1 - Real.exp y) ∂X.ν
  let C : ℝ := (X.ν (Iic (-(1 / ((k : ℝ) + 1))))).toReal ^ 2
  have hrange : Integrable W P ∧ Integrable L P ∧
      0 ≤ q ∧ q ≤ 1 := by
    simpa only [T, S, W, L, q] using
      (avram_bv_jump8_turn10_shortcell_original_marked_bochner_range
        X hX hBV k n)
  have hmark : (∫ ω, L ω ∂P) =
      (1 / ((n : ℝ) + 1)) * a := by
    simpa only [T, S, L, a] using
      (avram_bv_jump8_turn10_shortcell_original_mark_loss_real_mean
        X hX hBV k n)
  have hcoll : 0 ≤ ∫ ω, (W ω - (1 - L ω)) ∂P ∧
      (∫ ω, (W ω - (1 - L ω)) ∂P) ≤
        (1 / ((n : ℝ) + 1)) ^ 2 * C := by
    simpa only [T, S, W, L, C] using
      (avram_bv_jump8_turn10_shortcell_original_marked_collision_expectation
        X hX hBV k n)
  have hconst : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const _
  have hint :
      (∫ ω, (W ω - (1 - L ω)) ∂P) =
        q - (1 - ∫ ω, L ω ∂P) := by
    calc
      (∫ ω, (W ω - (1 - L ω)) ∂P) =
          (∫ ω, W ω ∂P) - (∫ ω, (1 - L ω) ∂P) := by
            simpa only [Pi.sub_apply] using
              (integral_sub hrange.1 (hconst.sub hrange.2.1))
      _ = q - (1 - ∫ ω, L ω ∂P) := by
        rw [show (∫ ω, (1 - L ω) ∂P) =
          (∫ ω, (1 : ℝ) ∂P) - (∫ ω, L ω ∂P) from by
            simpa only [Pi.sub_apply] using
              (integral_sub hconst hrange.2.1)]
        simp [q]
  have hident : (∫ ω, (W ω - (1 - L ω)) ∂P) =
      q - (1 - a / ((n + 1 : ℕ) : ℝ)) := by
    rw [hint, hmark]
    norm_cast
    ring
  refine ⟨hrange.2.2.1, hrange.2.2.2, ?_, ?_⟩
  · rw [← hident]
    exact hcoll.1
  · rw [← hident]
    calc
      (∫ ω, (W ω - (1 - L ω)) ∂P) ≤
          (1 / ((n : ℝ) + 1)) ^ 2 * C := hcoll.2
      _ = C / ((n + 1 : ℕ) : ℝ) ^ 2 := by
        simp only [Nat.cast_add, Nat.cast_one]
        have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp [hn]
