-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_countable_rightJump_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:28:28.923313+00:00
-- url     : https://prove2.me/submissions/c4c44fd9-a127-4255-bef1-be9edab1d29e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Countable
      {t : ℝ | Function.rightLim (fun s : ℝ => D s.toNNReal ω) t ≠
        D t.toNNReal ω} := by
  have hmono : Monotone (fun s : ℝ => D s.toNNReal ω) :=
    fun _ _ hab => (hD.2.1 ω) (Real.toNNReal_mono hab)
  apply hmono.countable_not_continuousAt.mono
  intro t ht
  by_contra hc
  have hcont : ContinuousAt (fun s : ℝ => D s.toNNReal ω) t :=
    not_not.mp hc
  have heq := hcont.continuousWithinAt.rightLim_eq
  exact ht heq
