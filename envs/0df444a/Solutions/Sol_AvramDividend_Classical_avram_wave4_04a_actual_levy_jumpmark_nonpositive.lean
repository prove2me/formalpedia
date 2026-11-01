-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_levy_jumpmark_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:41:54.470524+00:00
-- url     : https://prove2.me/submissions/85f88f8d-d130-4d93-a354-64cf6bf601b3

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (ω : Ω) (t : ℝ≥0), 0 < t →
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≤ 0 := by
  intro ω t ht
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have heq : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = l :=
    leftLim_eq_of_tendsto hl
  rw [heq]
  have hno := X.noPosJumps ω t l ht hl
  linarith
