-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_original_smallband_increment_shift_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:12:24.080192+00:00
-- url     : https://prove2.me/submissions/1ab06887-c683-49c7-9f55-e8e7712cc88a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_smallband_marked_window_difference_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_signed_negative_band_window_shift_borel_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A compensated original cutoff band is a Borel future-path statistic. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  classical
  obtain ⟨J, hJ, hJsource⟩ :=
    avram_a23_signed_negative_band_window_shift_borel_20261113
      X n s t hst
  let T : ℝ≥0 := t - s
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let m : ℝ := ∫ z in B, z ∂X.ν
  let W : (ℝ≥0 → ℝ) → ℝ := fun Y => J Y - (T : ℝ) * m
  refine ⟨W, hJ.sub_const ((T : ℝ) * m), ?_⟩
  intro ω
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
  have hWin : C t - C s =
      ∫ p in (Ioc s t ×ˢ B), p.2 ∂NX := by
    simpa [C, NX, B] using
      avram_a23_original_smallband_marked_window_difference_20261113
        X ω n s t hst
  have hBorel : (∫ p in (Ioc s t ×ˢ B), p.2 ∂NX) =
      J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
    simpa [NX, B] using hJsource ω
  have hCast : (T : ℝ) = (t : ℝ) - (s : ℝ) :=
    NNReal.coe_sub hst
  change
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
    J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) - (T : ℝ) * m
  rw [hUnfold t, hUnfold s]
  rw [← hBorel, ← hWin, hCast]
  ring
