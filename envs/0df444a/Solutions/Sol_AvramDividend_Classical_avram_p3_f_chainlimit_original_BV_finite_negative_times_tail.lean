-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_BV_finite_negative_times_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:42:10.053596+00:00
-- url     : https://prove2.me/submissions/3244aee1-586a-4d4f-bb47-3ca07fd6d0e0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_ae_small_jump_epsilon_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_ae_finite_strict_large_marks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let j : ℝ≥0 → ℝ := fun u =>
        if 0 < u ∧ u ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0
      ∀ ε : ℝ, 0 < ε →
        ∃ S : Finset ℝ≥0,
          (∀ t, t ∈ S → 0 < t ∧ t ≤ T) ∧
          (∑' t : ℝ≥0, if t ∈ S then 0 else |j t|) < ε := by
  filter_upwards
    [avram_p3_main_original_ae_small_jump_epsilon_cutoff X hBV T,
      avram_p3_main_original_ae_finite_strict_large_marks X hBV T]
    with ω hsmall hlarge
  intro j ε hε
  obtain ⟨δ, hδ, hTail⟩ := hsmall ε hε
  obtain ⟨hFinite, hTime⟩ := hlarge δ hδ
  let S : Finset ℝ≥0 := hFinite.toFinset
  have hmem (t : ℝ≥0) : t ∈ S ↔ δ ≤ |j t| := by
    simp [S, j]
  refine ⟨S, ?_, ?_⟩
  · intro t ht
    exact hTime t ((hmem t).mp ht)
  · have hfun :
        (fun t : ℝ≥0 => if t ∈ S then (0 : ℝ) else |j t|) =
          (fun t : ℝ≥0 => if |j t| < δ then |j t| else 0) := by
      funext t
      by_cases h : δ ≤ |j t|
      · have hs : t ∈ S := (hmem t).mpr h
        simp [hs, not_lt.mpr h]
      · have hlt : |j t| < δ := lt_of_not_ge h
        have hns : t ∉ S := by
          intro ht
          exact h ((hmem t).mp ht)
        simp [hns, hlt]
    rw [hfun]
    exact hTail
