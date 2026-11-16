-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_no_small_band_marks_compensator_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:37:15.751284+00:00
-- url     : https://prove2.me/submissions/9e519803-9470-431b-919f-c4194c393bb4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_intrinsic_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b27_marked_large_only_count_small_band_zero
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_nu_band_integral_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (ω : Ω)
    (hLarge : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (n : ℕ) (t : ℝ≥0) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω = 0 := by
  let S : Set ℝ≥0 := {u | 0 < u ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}
  let μ : Measure ℝ≥0 := Measure.count.restrict S
  let f : ℝ≥0 → ℝ≥0 × ℝ := fun u =>
    (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  have hf : AEMeasurable f μ :=
    (avram_b27_original_intrinsic_mark_map_measurable X ω).aemeasurable
  have hmarks : ∀ u, (f u).2 = 0 ∨ (f u).2 ≤ -1 := by
    intro u
    by_cases hu : u = 0
    · left
      have hleft := avram_p2_a_zero_rate_leftLim_origin_nnreal
        (fun v : ℝ≥0 => X.X v ω)
      simp [f, hu, hleft]
    · have hpos : 0 < u := lt_of_le_of_ne (show (0 : ℝ≥0) ≤ u from bot_le) (Ne.symm hu)
      simpa only [f] using hLarge u hpos
  have hCount :=
    avram_b27_marked_large_only_count_small_band_zero μ f hf hmarks n t
  have hComp :=
    avram_b27_original_no_small_nu_band_integral_zero X.ν hν n
  change
    (∫ p in (Ioc (0 : ℝ≥0) t ×ˢ
        Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))),
      p.2 ∂(μ.map f)) -
      (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))),
        z ∂X.ν) = 0
  rw [hCount, hComp]
  ring
