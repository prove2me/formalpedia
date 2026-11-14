-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB290_original_dividend_bad_cell_probability_time_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:17:36.801941+00:00
-- url     : https://prove2.me/submissions/dda0f16a-0260-417a-9889-4f24dc2cb710

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB284_original_bad_cell_prob_time_mass_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB289_original_dividend_fourth_power_mesh_endpoint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original dividend mesh bad-cell probability-time mass is bounded by localised dividend variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n m M : ℕ) (hm : 0 < m)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (hinc : ∀ ω, (Prod.mk ω ⁻¹' S) ⊆
      ⋃ i ∈ ((Finset.range (n * m ^ 4)).filter
        (fun i => 1 / ((m : ℝ) ^ 3) <
          D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω -
          D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω)),
      Set.Ioo ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))))
    (hloc : ∀ ω, (∃ t : ℝ, (ω, t) ∈ S) →
      D n ω - D 0 ω ≤ (M : ℝ)) :
    (P.prod volume) S ≤ ENNReal.ofReal ((M : ℝ) / (m : ℝ)) := by
  let d : Ω → ℕ → ℝ := fun ω i =>
    D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω
  have hgrid (ω : Ω) :=
    avram_gbB289_original_dividend_fourth_power_mesh_endpoint D hD ω n m hm
  have hdmono : ∀ ω, Monotone (d ω) := fun ω => (hgrid ω).1
  have hlocal : ∀ ω, (∃ t : ℝ, (ω, t) ∈ S) →
      d ω (n * m ^ 4) - d ω 0 ≤ (M : ℝ) := by
    intro ω hω
    have hend : d ω (n * m ^ 4) = D n ω := (hgrid ω).2.1
    have hstart : d ω 0 = D 0 ω := by simp [d]
    calc
      d ω (n * m ^ 4) - d ω 0 = D n ω - D 0 ω := by
        rw [hend, hstart]
      _ ≤ (M : ℝ) := hloc ω hω
  exact avram_gbB284_original_bad_cell_prob_time_mass_bound
    P d hdmono n m M hm S hS hinc hlocal
