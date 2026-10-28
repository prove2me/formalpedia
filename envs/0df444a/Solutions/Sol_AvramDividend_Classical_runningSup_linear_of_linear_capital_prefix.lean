-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_linear_of_linear_capital_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:54:23.2592+00:00
-- url     : https://prove2.me/submissions/507c22bb-b2a5-4678-a682-6a4469ffb3df

import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A linear nonnegative-drift capital prefix has a linear running record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (hDrift : 0 ≤ X.drift)
    (hLinear : ∀ u : ℝ≥0, u ≤ t →
      X.X u ω = X.drift * (u : ℝ)) :
    runningSup X t ω = X.drift * (t : ℝ) := by
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, by simp⟩⟩
  have hUpper (s : Set.Icc (0 : ℝ≥0) t) :
      X.X s.1 ω ≤ X.drift * (t : ℝ) := by
    rw [hLinear s.1 s.2.2]
    have hs : (s.1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast s.2.2
    exact mul_le_mul_of_nonneg_left hs hDrift
  have hBound : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω)) := by
    refine ⟨X.drift * (t : ℝ), ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hUpper s
  have hBelow : X.drift * (t : ℝ) ≤
      ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω := by
    have h := le_ciSup hBound
      (⟨t, by simp⟩ : Set.Icc (0 : ℝ≥0) t)
    simpa only [hLinear t le_rfl] using h
  rw [(runningSup_eq_rawSup_nonneg X t ω).1]
  exact le_antisymm (ciSup_le hUpper) hBelow
