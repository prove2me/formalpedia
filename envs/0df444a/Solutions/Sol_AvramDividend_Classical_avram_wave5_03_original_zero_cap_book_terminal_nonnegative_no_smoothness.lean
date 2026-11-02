-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_zero_cap_book_terminal_nonnegative_no_smoothness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:07:46.352797+00:00
-- url     : https://prove2.me/submissions/0776ecf1-609a-434f-b9c7-12e37441dd9d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCzero : C = 0)
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (riskProcess X x D t ω) := by
  let y : ℝ := riskProcess X x D t ω
  change 0 ≤ w y
  have hcap : ENNReal.ofReal y ≤ 0 := by
    by_cases hzero : t = 0
    · subst t
      have hs : IsDividendStrategy 𝓕 D := hD.1.1
      have hD0 : D 0 ω = 0 := hs.1 ω
      have hX0 : X.X 0 ω = 0 := X.X_zero ω
      simpa only [hCzero, y, riskProcess, hX0, hD0, sub_zero, add_zero]
        using hxc
    · have htpos : 0 < t :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm hzero)
      simpa only [hCzero] using hD.2 ω t htpos
  have hy0 : ENNReal.ofReal y = 0 :=
    le_antisymm hcap (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal y from zero_le)
  have hy : y ≤ 0 := ENNReal.ofReal_eq_zero.mp hy0
  by_cases hneg : y < 0
  · simpa only [hw_neg y hneg] using (le_refl (0 : ℝ))
  · have heq : y = 0 := le_antisymm hy (le_of_not_gt hneg)
    simpa only [heq] using hw0
