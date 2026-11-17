-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_occupied_Borel_grid_indicator_zero_one_and_card_sum_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:44:42.376214+00:00
-- url     : https://prove2.me/submissions/f2356eef-7487-4e55-9826-73a7af935141

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_range_occupied_card_equals_fin_boolean_sum_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    let Y : Fin n → Ω → ℕ := fun i ω =>
      if NX ω (Ioc ((i.val : ℝ≥0) * δ)
        (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) = 0
      then 0 else 1
    let Z : Ω → ℕ := fun ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ)
          (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) ≠ 0)).card
    (∀ i ω, Y i ω = 0 ∨ Y i ω = 1) ∧
      (∀ ω, Z ω = ∑ i : Fin n, Y i ω) := by
  classical
  dsimp only
  constructor
  · intro i ω
    split_ifs <;> simp
  · intro ω
    have h := avram_a26_range_occupied_card_equals_fin_boolean_sum_20261116
      n (fun i : ℕ =>
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc ((i : ℝ≥0) * (T / (n : ℝ≥0)))
            (((i + 1 : ℕ) : ℝ≥0) * (T / (n : ℝ≥0))) ×ˢ B)) ≠ 0)
    simpa only [ite_not] using h
