-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_physical_occupied_grid_count_measurable_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:36:54.047141+00:00
-- url     : https://prove2.me/submissions/506161a4-eb6a-4ff3-aeb7-e344162903a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
    let Z : ℕ → Ω → ℕ := fun n ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
    ∀ n : ℕ, Measurable (Z n) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
  let Z : ℕ → Ω → ℕ := fun n ω =>
    ((Finset.range n).filter (fun i : ℕ =>
      NX ω (Ioc ((i : ℝ≥0) * δ n)
        (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
  change ∀ n : ℕ, Measurable (Z n)
  intro n
  have hCell (i : ℕ) :
      Measurable (fun ω : Ω =>
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B)) := by
    have hh : (i : ℝ≥0) * δ n ≤ ((i + 1 : ℕ) : ℝ≥0) * δ n := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_succ i
      · exact bot_le
    simpa only [NX] using
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X ((i : ℝ≥0) * δ n) (((i + 1 : ℕ) : ℝ≥0) * δ n) hh B hB)
  have hEach (i : ℕ) :
      Measurable (fun ω : Ω => if
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0
        then (1 : ℕ) else 0) := by
    have hset : MeasurableSet {ω : Ω |
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0} :=
      ((hCell i) (measurableSet_singleton 0)).compl
    exact measurable_const.ite hset measurable_const
  have hEq : (fun ω : Ω => Z n ω) =
      (fun ω : Ω => ∑ i ∈ Finset.range n,
        if NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0
        then (1 : ℕ) else 0) := by
    funext ω
    simp only [Z, Finset.card_filter]
  have hsum : Measurable (fun ω : Ω => ∑ i ∈ Finset.range n,
        if NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0
        then (1 : ℕ) else 0) := by
    exact Finset.measurable_sum (Finset.range n) (fun i hi => hEach i)
  change Measurable (fun ω : Ω => Z n ω)
  rw [hEq]
  exact hsum
