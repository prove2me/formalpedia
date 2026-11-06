-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_inner_band_uniform_C1_J_commutator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:31:47.41587+00:00
-- url     : https://prove2.me/submissions/851ddd45-344b-45f1-83c3-94638c0d22c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_uniform_compact_C1_negative_J_shift_commutator
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_strict_compact_margin_absorbs_Y_shift_of_J_cell
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- One inner source negative-J segment suffices: margin and Y fineness certify the shifted C1 cell automatically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b a₀ b₀ : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ha : a < a₀) (hb : b₀ < b) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ),
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        let z : ℕ → ℝ := fun i =>
          x + X.X (u i) ω - rightLimit D (u i) ω
        let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
        let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
        (∀ i, i < n →
          Set.uIcc (z i - j i) (z i) ⊆ Set.Icc a₀ b₀) →
        (∀ i, i < n → |c i| < δ) →
        ∀ i, i < n →
          |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| ≤ ε * |j i| := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hControl⟩ :=
    avram_p3_f2_original_uniform_compact_C1_negative_J_shift_commutator
      X x C D hD w hwC1 hOpen a b hBand ε hε
  have hMargin : 0 < min (a₀ - a) (b - b₀) :=
    lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)
  let δ := min δ₀ (min (a₀ - a) (b - b₀))
  have hδ : 0 < δ := lt_min hδ₀ hMargin
  refine ⟨δ, hδ, ?_⟩
  intro ω u n J Y z c j hInner hSmall
  have hOuter : Set.Icc a₀ b₀ ⊆ Set.Icc a b := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hBase (i : ℕ) (hi : i < n) :
      Set.uIcc (z i - j i) (z i) ⊆ Set.Icc a b :=
    (hInner i hi).trans hOuter
  have hFineMargin (i : ℕ) (hi : i < n) :
      |c i| < min (a₀ - a) (b - b₀) :=
    lt_of_lt_of_le (hSmall i hi) (min_le_right _ _)
  have hShift :=
    avram_p3_f2_original_strict_compact_margin_absorbs_Y_shift_of_J_cell
      X x C D hD a b a₀ b₀ ha hb ω u n hInner hFineMargin
  have hFine (i : ℕ) (hi : i < n) : |c i| < δ₀ :=
    lt_of_lt_of_le (hSmall i hi) (min_le_left _ _)
  exact hControl ω u n hBase hShift hFine
