-- Prove2me | solution 1 for AvramDividend.Classical.levy_germ_negative_limsup_ae_of_uniform_mass_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:21:32.13852+00:00
-- url     : https://prove2.me/submissions/d941ccc5-a235-4340-a21a-f985a7bfa4ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_probability_limsup_uniform_lower_mass_ws01f
import Theorems.Thm_AvramDividend_Classical_germ_negative_slope_limsup_measurable_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_germ_zero_one_ws01f

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (C p : ℝ) (hp : 0 < p) (N : ℕ)
    (hmass : ∀ n ≥ N,
      p ≤ P.real {ω | X.X (δ n) ω < C * (δ n : ℝ)}) :
    ∀ᵐ ω ∂P,
      ω ∈ (⋂ k : ℕ, ⋃ n : ℕ,
        {ω : Ω | k ≤ n ∧ X.X (δ n) ω < C * (δ n : ℝ)}) := by
  haveI := X.isProbability
  have hXm : ∀ t, Measurable (X.X t) := fun t =>
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hA : ∀ n, MeasurableSet {ω | X.X (δ n) ω < C * (δ n : ℝ)} := fun n =>
    measurableSet_lt (hXm _) measurable_const
  set S := ⋂ k : ℕ, ⋃ n : ℕ, {ω : Ω | k ≤ n ∧ X.X (δ n) ω < C * (δ n : ℝ)} with hS
  have hSm : MeasurableSet S := by
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun n => ?_
    by_cases hkn : k ≤ n
    · simpa [hkn] using hA n
    · simp [hkn]
  have hlow := AvramDividend.Classical.probability_limsup_uniform_lower_mass_ws01f
    (μ := P) (fun n => {ω | X.X (δ n) ω < C * (δ n : ℝ)}) hA p hp N hmass
  have hgerm := AvramDividend.Classical.germ_negative_slope_limsup_measurable_ws01f X.X δ hδ C
  rcases AvramDividend.Classical.levy_germ_zero_one_ws01f X hgerm with h0 | h1
  · exfalso
    have : P.real S = 0 := by rw [Measure.real, show P S = 0 from h0]; rfl
    simp only [mem_setOf_eq] at hlow
    rw [← hS] at hlow
    linarith
  · rw [ae_iff]
    have : P Sᶜ = 0 := by rw [prob_compl_eq_zero_iff hSm]; exact h1
    simpa [compl_def] using this
