-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_bounded_mark_integral_ae_count_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:14:30.541211+00:00
-- url     : https://prove2.me/submissions/61cf0a20-73fd-4a0c-b439-f3dee9bf77bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ))
    (g : ℝ → ℝ) (hg : Measurable g)
    (hBound : ∀ z ∈ B, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let C : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ B
    ∀ᵐ ω ∂P,
      IntegrableOn (fun p : ℝ≥0 × ℝ => g p.2) C (NX ω) ∧
      |∫ p in C, g p.2 ∂NX ω| ≤ (NX ω C).toReal := by
  intro NX C
  have hAll : ∀ᵐ ω ∂P,
      NX ω (Ioc 0 T ×ˢ Iio (0 : ℝ)) ≠ ⊤ := by
    simpa only [NX] using
      (avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
        X hFinite T)
  have hSub : C ⊆ Ioc 0 T ×ˢ Iio (0 : ℝ) := by
    intro p hp
    exact ⟨hp.1, hNeg hp.2⟩
  filter_upwards [hAll] with ω hw
  have hFiniteCell : NX ω C < ⊤ :=
    lt_of_le_of_lt (measure_mono hSub) (lt_top_iff_ne_top.mpr hw)
  exact avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
    (NX ω) T B hB g hg hFiniteCell hBound
