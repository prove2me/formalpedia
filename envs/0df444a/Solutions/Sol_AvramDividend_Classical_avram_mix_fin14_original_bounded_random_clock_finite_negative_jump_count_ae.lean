-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin14_original_bounded_random_clock_finite_negative_jump_count_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:23:24.231405+00:00
-- url     : https://prove2.me/submissions/d861e19d-4cec-437d-8cc6-47dd07a35bb7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded random clock inherits finite literal jump activity from its deterministic ceiling. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) ≠ ⊤ := by
  have hN :=
    avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
      X hFinite (n : ℝ≥0)
  filter_upwards [hN] with ω hω
  let J : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hSet : (Ioc (0 : ℝ≥0) (σ ω) ×ˢ Iio (0 : ℝ)) ⊆
      (Ioc (0 : ℝ≥0) (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (hBound ω)⟩, hp.2⟩
  have hle : J (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) ≤
      J (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) :=
    measure_mono hSet
  have hn : J (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hω
  exact ne_of_lt (lt_of_le_of_lt hle hn)
