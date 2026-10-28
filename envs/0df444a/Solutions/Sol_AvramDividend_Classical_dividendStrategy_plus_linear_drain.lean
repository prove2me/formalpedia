-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_plus_linear_drain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:51:21.610308+00:00
-- url     : https://prove2.me/submissions/b1711c4e-5836-4fa3-8671-8e22f1bdab17

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Adding a deterministic unit-rate dividend drain preserves the defining
    monotonicity, left-continuity, adaptedness and zero-start properties. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    IsDividendStrategy 𝓕 (fun t ω => D t ω + (t : ℝ)) := by
  rcases hD with ⟨hzero, hmono, hcont, hadapt⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    simp [hzero ω]
  · intro ω s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    exact add_le_add (hmono ω hst) hst'
  · intro ω t
    exact (hcont ω t).add NNReal.continuous_coe.continuousWithinAt
  · intro t
    exact (hadapt t).add measurable_const
