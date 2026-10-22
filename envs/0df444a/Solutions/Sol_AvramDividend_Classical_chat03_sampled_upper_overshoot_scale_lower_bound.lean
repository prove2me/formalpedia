-- Prove2me | solution 1 for AvramDividend.Classical.chat03_sampled_upper_overshoot_scale_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:58:05.418452+00:00
-- url     : https://prove2.me/submissions/1b7be8fc-1aea-4470-a05e-72aa5d325ffc

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-!
At a sampled strict upper crossing, an upward reserve overshoot can
increase the q-scale payoff. The correct comparison is an inequality.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a)
    (t : ℝ≥0) (ω : Ω) (hcross : a - x < X.X t ω) :
    Real.exp (-(q * (t : ℝ))) * W a ≤
      Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) := by
  have ha0 : 0 ≤ a := ha.le
  have hay : a ≤ x + X.X t ω := by linarith
  have hy0 : 0 ≤ x + X.X t ω := ha0.trans hay
  have hWle : W a ≤ W (x + X.X t ω) :=
    hW.2.2.2.1 (Set.mem_Ici.mpr ha0)
      (Set.mem_Ici.mpr hy0) hay
  exact mul_le_mul_of_nonneg_left hWle (Real.exp_nonneg _)
