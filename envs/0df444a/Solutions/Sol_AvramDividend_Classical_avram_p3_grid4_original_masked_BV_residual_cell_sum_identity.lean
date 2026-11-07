-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_masked_BV_residual_cell_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:28:19.154554+00:00
-- url     : https://prove2.me/submissions/2a5dbc55-4d5e-46e3-9335-0381acd64432

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original BV drift residual algebra under arbitrary physical-cell masks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    (∑ i ∈ Finset.range n, a i * (R (u i) - R (u (i + 1)))) =
      ∑ i ∈ Finset.range n, a i *
        ((X.X (u (i + 1)) ω - X.X (u i) ω) +
         (J (u (i + 1)) - J (u i)) -
         (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) := by
  dsimp
  apply Finset.sum_congr rfl
  intro i hi
  ring
