-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_strict_compact_margin_absorbs_Y_shift_of_J_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:27:03.240457+00:00
-- url     : https://prove2.me/submissions/67a173ce-5a7b-4cde-826d-2be167a1dc7a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A finite strict compact reserve margin absorbs every sufficiently small actual Y displacement of a raw-J segment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (a b a₀ b₀ : ℝ) (ha : a < a₀) (hb : b₀ < b) :
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
      (∀ i, i < n → |c i| < min (a₀ - a) (b - b₀)) →
      ∀ i, i < n →
        Set.uIcc (z i + c i - j i) (z i + c i) ⊆
          Set.Icc a b := by
  intro ω u n J Y z c j hInside hSmall i hi t ht
  have hLeft : |c i| < a₀ - a :=
    lt_of_lt_of_le (hSmall i hi) (min_le_left _ _)
  have hRight : |c i| < b - b₀ :=
    lt_of_lt_of_le (hSmall i hi) (min_le_right _ _)
  have hcLeft : -(a₀ - a) < c i := (abs_lt.mp hLeft).1
  have hcRight : c i < b - b₀ := (abs_lt.mp hRight).2
  have hUnshift : t - c i ∈ Set.uIcc (z i - j i) (z i) := by
    rcases Set.mem_uIcc.mp ht with h | h
    · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩)
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩)
  have hBand := hInside i hi hUnshift
  exact ⟨by linarith [hBand.1], by linarith [hBand.2]⟩
