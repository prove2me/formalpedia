-- Prove2me | solution 1 for AvramDividend.Classical.chat03_no_exit_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:41:21.484563+00:00
-- url     : https://prove2.me/submissions/fee28067-4f61-4b28-87af-87faa6672fe5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
If continuous strict passage has not occurred before the finite horizon,
no sampled point strictly before that horizon can be a genuine strict exit.
This handles the no-exit and horizon-equality branches of capped grids.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hTτ : T ≤ τ) :
    ∀ h : ℝ≥0, ∀ k : ℕ,
      (k : ℝ≥0) * h < T →
        ¬ (X.X ((k : ℝ≥0) * h) ω < lower ∨
           upper < X.X ((k : ℝ≥0) * h) ω) := by
  intro h k hkT hExit
  have hτk : τ ≤ (k : ℝ≥0) * h := hτ.1 hExit
  exact (not_lt_of_ge (hTτ.trans hτk)) hkT
