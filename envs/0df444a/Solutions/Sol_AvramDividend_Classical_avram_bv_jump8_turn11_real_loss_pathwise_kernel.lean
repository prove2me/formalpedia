-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn11_real_loss_pathwise_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:48:42.175229+00:00
-- url     : https://prove2.me/submissions/7a9e0ada-0b5c-42a9-9e78-6fc5ef63a96f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_intrinsic_weighted_sum
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_real_loss_ofReal_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The physical pathwise kernel identity is the composite of a restricted
intrinsic integral-to-sum theorem and a finite positive real-loss conversion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
    let B : Set ℝ := Iio (-ε)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    ∀ ω : Ω, 0 ≤ L ω ∧
      (∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
        (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ENNReal.ofReal (L ω) := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let ε : ℝ := 1 / ((k : ℝ) + 1)
  let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
  let B : Set ℝ := Iio (-ε)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let K : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
      (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hsum : ∀ ω : Ω, K ω =
      ∑ u ∈ S ω, ENNReal.ofReal
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
    simpa only [T, ε, φ, B, S, K] using
      (avram_bv_jump8_turn12_intrinsic_weighted_sum X hX hBV k n)
  have hreal : ∀ ω : Ω, 0 ≤ L ω ∧
      (∑ u ∈ S ω, ENNReal.ofReal
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      ENNReal.ofReal (L ω) := by
    simpa only [T, S, L] using
      (avram_bv_jump8_turn12_real_loss_ofReal_sum X hX hBV k n)
  change ∀ ω : Ω, 0 ≤ L ω ∧ K ω = ENNReal.ofReal (L ω)
  intro ω
  constructor
  · exact (hreal ω).1
  · calc
      K ω = ∑ u ∈ S ω, ENNReal.ofReal
          (1 - Real.exp (X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)) := hsum ω
      _ = ENNReal.ofReal (L ω) := (hreal ω).2
