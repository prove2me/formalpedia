-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_uniform_compensated_band_future_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:34:31.70339+00:00
-- url     : https://prove2.me/submissions/3838853e-3736-45e7-9b7f-22ef3d70a847

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_smallband_marked_window_difference_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_uniform_signed_negative_band_window_borel_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single source future-path statistic gives every translated compensated band increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T : ℝ≥0) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s + T) ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  classical
  obtain ⟨J, hJ, hWindow⟩ :=
    avram_a23_uniform_signed_negative_band_window_borel_20261113 X n T
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let m : ℝ := ∫ z in B, z ∂X.ν
  let W : (ℝ≥0 → ℝ) → ℝ := fun Y => J Y - (T : ℝ) * m
  refine ⟨W, hJ.sub_const ((T : ℝ) * m), ?_⟩
  intro s ω
  let NX : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let C : ℝ≥0 → ℝ := fun u =>
    ∫ p in (Ioc (0 : ℝ≥0) u ×ˢ B), p.2 ∂NX
  have hUnfold (u : ℝ≥0) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω =
      C u - (u : ℝ) * m := by
    rfl
  have hWin : C (s + T) - C s =
      ∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂NX := by
    simpa [C, NX, B] using
      avram_a23_original_smallband_marked_window_difference_20261113
        X ω n s (s + T) (le_add_of_nonneg_right zero_le)
  have hBorel : (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂NX) =
      J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
    simpa [NX, B] using hWindow s ω
  change
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s + T) ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
    J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) - (T : ℝ) * m
  rw [hUnfold (s + T), hUnfold s]
  rw [← hBorel, ← hWin, NNReal.coe_add]
  ring
