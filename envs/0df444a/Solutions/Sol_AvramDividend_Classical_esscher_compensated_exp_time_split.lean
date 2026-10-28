-- Prove2me | solution 1 for AvramDividend.Classical.esscher_compensated_exp_time_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:58:35.266314+00:00
-- url     : https://prove2.me/submissions/1244e958-04ec-4b01-9453-ac22f815ff36

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-- The Esscher weight factors into past and compensated future-increment weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (s u : ℝ≥0) (ω : Ω) :
    Real.exp
      (θ * X.X (s + u) ω -
        ((s + u : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
    Real.exp
      (θ * X.X s ω -
        (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
    Real.exp
      (θ * (X.X (s + u) ω - X.X s ω) -
        (u : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring
