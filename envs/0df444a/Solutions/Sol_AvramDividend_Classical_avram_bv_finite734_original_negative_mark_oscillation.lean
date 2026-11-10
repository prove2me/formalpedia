-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_finite734_original_negative_mark_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:48:32.649301+00:00
-- url     : https://prove2.me/submissions/37f76de0-18af-414f-8e73-37f33c736562

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_closed_both_boundaries_HJB_lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hactivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y z : ℝ, y ∈ Icc (0 : ℝ) ε → z < 0 →
        |w (y + z) - w y| ≤ K := by
  obtain ⟨L, hL, hLip⟩ :=
    avram_bv_zero13_finite_activity_closed_both_boundaries_HJB_lipschitz
      X hX hBV hactivity q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad ε hε hεC
  let B : ℝ := |w 0| + L * ε
  have hB : 0 ≤ B :=
    add_nonneg (abs_nonneg _) (mul_nonneg hL (le_of_lt hε))
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) ε :=
    ⟨le_refl _, le_of_lt hε⟩
  have hbound : ∀ y ∈ Icc (0 : ℝ) ε, |w y| ≤ B := by
    intro y hy
    have hLipy := hLip 0 hzero y hy
    have htriangle : |w y| ≤ |w y - w 0| + |w 0| := by
      calc
        |w y| = |(w y - w 0) + w 0| := by ring
        _ ≤ |w y - w 0| + |w 0| := abs_add_le _ _
    have hy0 : 0 ≤ y := hy.1
    have hyε : y ≤ ε := hy.2
    calc
      |w y| ≤ |w y - w 0| + |w 0| := htriangle
      _ ≤ L * |y - (0 : ℝ)| + |w 0| := by
        linarith [hLipy]
      _ = L * y + |w 0| := by rw [sub_zero, abs_of_nonneg hy0]
      _ ≤ L * ε + |w 0| := by
        have hmul := mul_le_mul_of_nonneg_left hyε hL
        linarith
      _ = B := by dsimp [B]; ring
  refine ⟨2 * B, by linarith, ?_⟩
  intro y z hy hz
  by_cases hyz : 0 ≤ y + z
  · have hz_le : y + z ≤ ε := by linarith [hy.2]
    have hpost : y + z ∈ Icc (0 : ℝ) ε := ⟨hyz, hz_le⟩
    have hfirst := hbound (y + z) hpost
    have hsecond := hbound y hy
    calc
      |w (y + z) - w y| ≤ |w (y + z)| + |w y| := by
        simpa [sub_eq_add_neg] using
          (abs_add_le (w (y + z)) (-w y))
      _ ≤ B + B := add_le_add hfirst hsecond
      _ = 2 * B := by ring
  · have hneg : y + z < 0 := lt_of_not_ge hyz
    rw [hw_neg (y + z) hneg]
    have hlast := hbound y hy
    have heq : |(0 : ℝ) - w y| = |w y| := by simp
    rw [heq]
    linarith
