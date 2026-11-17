-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_Borel_occupancy_disagreement_probability_vanishes_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:14:36.880206+00:00
-- url     : https://prove2.me/submissions/3ff1d5e4-d225-469e-83a7-c5d928bf94c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_Borel_physical_count_grid_occupancy_coupling_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_quadratic_uniform_cell_collision_budget_vanishes_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal) :
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
    Tendsto (fun n : ℕ => (P {ω : Ω | K ω ≠ Z n ω}).toReal)
      atTop (𝓝 (0 : ℝ)) := by
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
  let a : ℝ := (T : ℝ) * (X.ν B).toReal
  have hCell (n : ℕ) :
      (((δ n : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal = a / (n : ℝ) := by
    dsimp only [δ, a]
    rw [ENNReal.toReal_mul]
    simp only [ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_natCast]
    ring
  have hUpper : Tendsto (fun n : ℕ =>
      (n : ℝ) * (((((δ n : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ^ 2 / 2))
      atTop (𝓝 (0 : ℝ)) := by
    convert (avram_a26_quadratic_uniform_cell_collision_budget_vanishes_20261116 a) using 1
    funext n
    rw [hCell n]
  have hSource :=
    avram_a26_original_Borel_physical_count_grid_occupancy_coupling_20261116
      X hFinite T B hB hNeg K hK hCount
  have hBound : ∀ᶠ n : ℕ in atTop,
      (P {ω : Ω | K ω ≠ Z n ω}).toReal ≤
        (n : ℝ) * (((((δ n : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ^ 2 / 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simpa only [NX, δ, Z] using hSource n hn
  have hNonneg : ∀ n : ℕ,
      0 ≤ (P {ω : Ω | K ω ≠ Z n ω}).toReal := by
    intro n
    exact ENNReal.toReal_nonneg
  change Tendsto (fun n : ℕ =>
    (P {ω : Ω | K ω ≠ Z n ω}).toReal) atTop (𝓝 (0 : ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpper (Filter.Eventually.of_forall hNonneg) hBound
