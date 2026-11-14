-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_uniform_last_reserve_drift_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:12:06.215638+00:00
-- url     : https://prove2.me/submissions/4c25da86-7a27-44a8-b480-c726b9c23635

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      (x + X.X S ω - rightLimit D S ω) -
        (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ≤
        (T / ((m : ℝ) + 2)) * max X.drift 0 := by
  dsimp only
  filter_upwards
    [avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
      X hBV x D hD] with ω hω
  intro m
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have hden0 : (m : ℝ) + 2 ≠ 0 := ne_of_gt hden
  have hstep : ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) + 2 := by
    push_cast
    linarith
  have hlast : u m (m + 1) ≤ S := by
    change (u m (m + 1) : ℝ) ≤ T
    rw [huniform m (m + 1)]
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left hstep (le_of_lt hT)
  have hgap : (S : ℝ) - (u m (m + 1) : ℝ) =
      T / ((m : ℝ) + 2) := by
    change T - (u m (m + 1) : ℝ) =
      T / ((m : ℝ) + 2)
    rw [huniform m (m + 1)]
    push_cast
    field_simp
    ring
  have hUp := hω (u m (m + 1)) S hlast
  rw [hgap] at hUp
  exact hUp.trans (mul_le_mul_of_nonneg_left (le_max_left _ _)
    (div_nonneg (le_of_lt hT) (le_of_lt hden)))
