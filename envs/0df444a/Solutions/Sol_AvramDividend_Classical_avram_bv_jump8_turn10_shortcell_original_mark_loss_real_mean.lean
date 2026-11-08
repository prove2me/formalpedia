-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_mark_loss_real_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:44:35.655905+00:00
-- url     : https://prove2.me/submissions/2b436e35-8d8e-427d-9a4f-75972df24710

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux18_original_strict_negative_mark_loss_compensator
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_original_real_loss_to_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_levy_real_mark_loss_conversion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The source Campbell law combines with two real-valued conversion
certificates to give the literal short-cell original marked-loss mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    (∫ ω, L ω ∂P) =
      (1 / ((n : ℝ) + 1)) *
      (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν) := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let ε : ℝ := 1 / ((k : ℝ) + 1)
  let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
  let B : Set ℝ := Iio (-ε)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let M : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let C : ℝ≥0∞ := ∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
    (B.indicator φ) p.2 ∂M ω ∂P
  let D : ℝ≥0∞ := (T : ℝ≥0∞) * (∫⁻ y in B, φ y ∂X.ν)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hreal : (∫ ω, L ω ∂P) = C.toReal := by
    simpa only [T, ε, φ, B, S, L, C, M] using
      (avram_bv_jump8_turn11_original_real_loss_to_lintegral X hX hBV k n)
  have hcamp : C = D := by
    simpa only [C, D, M, B, φ] using
      (avram_redux18_original_strict_negative_mark_loss_compensator X T ε hε)
  have hdet : D.toReal =
      (1 / ((n : ℝ) + 1)) *
      (∫ y in Iio (-(1 / ((k : ℝ) + 1))),
        (1 - Real.exp y) ∂X.ν) := by
    simpa only [T, ε, B, φ, D] using
      (avram_bv_jump8_turn11_levy_real_mark_loss_conversion X hX hBV k n)
  calc
    (∫ ω, L ω ∂P) = C.toReal := hreal
    _ = D.toReal := congrArg ENNReal.toReal hcamp
    _ = _ := hdet
