-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_stopped_compact_C1_jump_cell_four_pairs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:39:38.85605+00:00
-- url     : https://prove2.me/submissions/9992171a-fb4a-44fa-8620-c519096ae3f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_C1_open_interior_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_jump_cell_four_pairs_of_local_Lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original stopped jump pairs inherit one compact C1 interior constant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a / 2 ≤ b)
    (hBand : Set.Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    (∀ i, i < n → z i ∈ Set.Icc (a / 2) b ∧
      z i + c i ∈ Set.Icc (a / 2) b ∧
      z i - j i ∈ Set.Icc (a / 2) b ∧
      z i + c i - j i ∈ Set.Icc (a / 2) b) →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i, i < n →
      (|w (z i + c i - j i) - w (z i - j i)| ≤ L * |c i|) ∧
      (|w (z i + c i) - w (z i)| ≤ L * |c i|) ∧
      (|w (z i + c i - j i) - w (z i + c i)| ≤ L * |j i|) ∧
      (|w (z i - j i) - w (z i)| ≤ L * |j i|) := by
  intro J Y z c j hPts
  obtain ⟨L, hL, hLip⟩ :=
    avram_p3_e_compensator_original_C1_open_interior_Lipschitz
      w a b hab _
      (avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C)
      hwC1 hBand
  refine ⟨L, hL, ?_⟩
  exact avram_p3_f2_original_stopped_jump_cell_four_pairs_of_local_Lipschitz
    X x C D hD w L (Set.Icc (a / 2) b) ω u n hPts hLip
