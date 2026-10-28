-- Prove2me | solution 1 for AvramDividend.Classical.isStoppingTime_iSup_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:50:40.015305+00:00
-- url     : https://prove2.me/submissions/f35b2af5-42f3-4c69-990f-dfbcc52047a8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    {κ : Type*} [Countable κ]
    (τ : κ → Ω → WithTop ℝ≥0)
    (hτ : ∀ k : κ, IsStoppingTime 𝓕 (τ k)) :
    IsStoppingTime 𝓕 (fun ω : Ω => ⨆ k : κ, τ k ω) := by
  intro t
  have hEq :
      {ω : Ω | (⨆ k : κ, τ k ω) ≤ (t : WithTop ℝ≥0)} =
        ⋂ k : κ, {ω : Ω | τ k ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, iSup_le_iff]
  rw [hEq]
  exact MeasurableSet.iInter (fun k => hτ k t)
