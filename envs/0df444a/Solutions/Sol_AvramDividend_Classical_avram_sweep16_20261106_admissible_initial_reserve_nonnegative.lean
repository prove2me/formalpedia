-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_admissible_initial_reserve_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:42:19.513472+00:00
-- url     : https://prove2.me/submissions/163a1256-c808-40c7-a569-f0709a53fbd8

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) : 0 ≤ x := by
  classical
  by_contra hx
  have hNo : IsEmpty Ω := ⟨fun ω => by
    have hstart := avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
      X x D hD.1 ω
    have hreserve : 0 ≤ x := by
      rcases hstart with ⟨hjump, hpost, _⟩
      rw [X.X_zero ω] at hpost
      linarith
    exact hx hreserve⟩
  letI : IsEmpty Ω := hNo
  have hEmpty : (Set.univ : Set Ω) = ∅ := by
    ext ω
    exact isEmptyElim ω
  have hZero : P (Set.univ : Set Ω) = 0 := by simp [hEmpty]
  letI : IsProbabilityMeasure P := X.isProbability
  have hOne : P (Set.univ : Set Ω) = 1 := measure_univ
  rw [hZero] at hOne
  norm_num at hOne
