-- Prove2me | solution 1 for AvramDividend.Classical.bv_path_residual_monotone_of_increment_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:17:37.069797+00:00
-- url     : https://prove2.me/submissions/09c2f6bf-5479-44a7-a909-5edbb991a2a2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every path with drift-bounded ordered increments has a monotone drift deficit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω)
    (hinc : ∀ s t : ℝ≥0, s ≤ t →
      X.X t ω - X.X s ω ≤ ((t - s : ℝ≥0) : ℝ) * X.drift) :
    Monotone (fun t : ℝ≥0 => (t : ℝ) * X.drift - X.X t ω) := by
  intro s t hst
  have h := hinc s t hst
  have hcoe : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) :=
    NNReal.coe_sub hst
  rw [hcoe] at h
  dsimp
  linarith
