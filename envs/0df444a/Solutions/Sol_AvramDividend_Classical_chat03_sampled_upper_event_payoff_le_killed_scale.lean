-- Prove2me | solution 1 for AvramDividend.Classical.chat03_sampled_upper_event_payoff_le_killed_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:58:02.124809+00:00
-- url     : https://prove2.me/submissions/dca68748-248b-4edb-91e9-a98960cea950

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
Compare the sampled upper-exit discount reward with the q-scale payoff
killed at a sampled lower exit. Grid overshoot gives an inequality.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a)
    (t : ℝ≥0) (ω : Ω) :
    (if a - x < X.X t ω then
        Real.exp (-(q * (t : ℝ))) * W a else 0) ≤
      (if X.X t ω < -x then 0 else
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) := by
  by_cases hdown : X.X t ω < -x
  · have hnup : ¬ a - x < X.X t ω := by linarith
    simp [hdown, hnup]
  · have hy : 0 ≤ x + X.X t ω := by linarith
    by_cases hup : a - x < X.X t ω
    · have ha0 : 0 ≤ a := ha.le
      have hay : a ≤ x + X.X t ω := by linarith
      have hWle : W a ≤ W (x + X.X t ω) :=
        hW.2.2.2.1 (Set.mem_Ici.mpr ha0)
          (Set.mem_Ici.mpr hy) hay
      simpa [hdown, hup] using
        (mul_le_mul_of_nonneg_left hWle (Real.exp_nonneg _))
    · simpa [hdown, hup] using
        (mul_nonneg (Real.exp_nonneg _) (hW.2.1 _ hy))
