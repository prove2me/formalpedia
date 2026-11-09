-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T21:29:41.523968+00:00
-- url     : https://prove2.me/submissions/b1fbabe6-a24a-4ef4-849a-9fe71c5416c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_mark_band_void_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- On a bounded clock, every sufficiently small negative original mark band is empty. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ B : Set ℝ, MeasurableSet B → B ⊆ Ioo (-ε) 0 →
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) = 0 := by
  classical
  have hGap := avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae X hFinite
  filter_upwards [hGap] with ω hω
  intro T
  obtain ⟨ε, hε, hJumpGap⟩ := hω T
  refine ⟨ε, hε, ?_⟩
  intro B hBm hBsmall
  have hBneg : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact (hBsmall hz).2
  apply (avram_wave7_06_original_intrinsic_negative_mark_band_void_iff
    X ω T B hBm hBneg).mp
  intro u hu hmark
  have hmark_neg : X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 :=
    (hBsmall hmark).2
  have hmark_ne : X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    linarith
  have hlarge := hJumpGap u hu.1 hu.2 hmark_ne
  have hsmall := (hBsmall hmark).1
  rw [abs_of_neg hmark_neg] at hlarge
  linarith
