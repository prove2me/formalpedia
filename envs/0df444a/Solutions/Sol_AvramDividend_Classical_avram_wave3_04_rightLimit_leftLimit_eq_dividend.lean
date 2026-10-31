-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_rightLimit_leftLimit_eq_dividend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:30:40.870468+00:00
-- url     : https://prove2.me/submissions/246c5717-aeba-4b0c-9442-4c9dd8939520

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Strict-right dividend modifications have original left-continuous
payments as their left limits, including singular continuous mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun s : ℝ≥0 => rightLimit D s ω)
      (𝓝[<] t) (𝓝 (D t ω)) := by
  rcases hD with ⟨hzero, hmono, hleft, hadapt⟩
  have hleftD : ContinuousWithinAt (fun s : ℝ≥0 => D s ω)
      (Iio t) t := (hleft ω t).mono (by
        intro s hs
        exact le_of_lt (Set.mem_Iio.mp hs))
  have hlow : ∀ᶠ s in 𝓝[<] t, D s ω ≤ rightLimit D s ω := by
    filter_upwards [] with s
    exact dividendStrategy_le_rightLimit D
      ⟨hzero, hmono, hleft, hadapt⟩ ω s
  have hupp : ∀ᶠ s in 𝓝[<] t, rightLimit D s ω ≤ D t ω := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hb : BddBelow (Set.range (fun u : Ioi s => D u.1 ω)) := by
      refine ⟨D 0 ω, ?_⟩
      rintro y ⟨u, rfl⟩
      exact hmono ω (bot_le : (0 : ℝ≥0) ≤ u.1)
    unfold rightLimit
    exact ciInf_le hb ⟨t, Set.mem_Ioi.mpr hs⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hleftD.tendsto tendsto_const_nhds hlow hupp
