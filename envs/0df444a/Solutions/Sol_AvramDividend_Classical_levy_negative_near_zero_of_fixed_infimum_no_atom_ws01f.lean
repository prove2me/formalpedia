-- Prove2me | solution 1 for AvramDividend.Classical.levy_negative_near_zero_of_fixed_infimum_no_atom_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:16:34.846648+00:00
-- url     : https://prove2.me/submissions/67775fe6-4c4c-4943-9e38-4364f2c35f05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_negative_running_infimum_nonneg
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival

open Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hAtom : ∀ (t : ℝ≥0), 0 < t →
      P {ω : Ω |
        -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} = 0} = 0) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ≥0), 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 := by
  have hP := X.isProbability
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P,
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (1 / ((n : ℝ≥0) + 1)) ∧ y = X.X s ω} ≠ 0 := by
    intro n
    have h := hAtom (1 / ((n : ℝ≥0) + 1)) (by positivity)
    rw [measure_eq_zero_iff_ae_notMem] at h
    filter_upwards [h] with ω hω
    exact hω
  rw [← ae_all_iff] at hn
  filter_upwards [hn] with ω hω
  intro ε hε
  obtain ⟨n, hnε⟩ := exists_nat_one_div_lt (show (0:ℝ) < ε from hε)
  have hpos := chat04_negative_running_infimum_nonneg X (1 / ((n : ℝ≥0) + 1)) ω
  have hlt : ¬ (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (1 / ((n : ℝ≥0) + 1)) ∧ y = X.X s ω} ≤ 0) := by
    intro h; exact hω n (le_antisymm h hpos)
  rw [chat04_reflected_infimum_Iic_iff_survival] at hlt
  push Not at hlt
  obtain ⟨s, hs, hXs⟩ := hlt
  refine ⟨s, lt_of_le_of_lt hs ?_, by simpa using hXs⟩
  rw [← NNReal.coe_lt_coe]
  simpa using hnε
