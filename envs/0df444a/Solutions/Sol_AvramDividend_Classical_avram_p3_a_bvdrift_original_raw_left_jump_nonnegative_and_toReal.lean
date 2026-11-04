-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:15:52.474873+00:00
-- url     : https://prove2.me/submissions/e3635ccd-919b-42a6-9fda-b89c0bee145e

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every positive-time original negative left-jump magnitude is nonnegative,
and its ENNReal representation converts back to the raw real source jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    0 ≤ Function.leftLim (fun u : ℝ≥0 => X.X u ω) t - X.X t ω ∧
      (ENNReal.ofReal (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t - X.X t ω)).toReal = Function.leftLim (fun u : ℝ≥0 => X.X u ω) t - X.X t ω := by
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  have hleft :
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = l :=
    leftLim_eq_of_tendsto hl
  have hnonneg :
      0 ≤ Function.leftLim (fun u : ℝ≥0 => X.X u ω) t - X.X t ω := by
    rw [hleft]
    exact sub_nonneg.mpr (X.noPosJumps ω t l ht hl)
  exact ⟨hnonneg, ENNReal.toReal_ofReal hnonneg⟩
