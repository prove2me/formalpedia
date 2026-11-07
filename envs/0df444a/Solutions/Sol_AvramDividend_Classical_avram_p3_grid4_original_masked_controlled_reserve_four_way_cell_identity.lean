-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_masked_controlled_reserve_four_way_cell_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:39:59.52021+00:00
-- url     : https://prove2.me/submissions/1c476b47-d957-4e00-b944-91b8feb684a9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact original BV reserve algebra retained under arbitrary stopped-cell masks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    let U : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    (∑ i ∈ Finset.range n, a i * (U (u (i + 1)) - U (u i))) =
      (∑ i ∈ Finset.range n, a i *
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) +
      (∑ i ∈ Finset.range n, a i * (R (u i) - R (u (i + 1)))) -
      (∑ i ∈ Finset.range n, a i * (J (u (i + 1)) - J (u i))) -
      (∑ i ∈ Finset.range n, a i *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by
  dsimp
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
