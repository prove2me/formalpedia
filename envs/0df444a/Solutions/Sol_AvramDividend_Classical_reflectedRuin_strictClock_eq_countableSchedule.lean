-- Prove2me | solution 1 for AvramDividend.Classical.reflectedRuin_strictClock_eq_countableSchedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:22:09.416059+00:00
-- url     : https://prove2.me/submissions/34fb44d5-cc17-42ff-9f68-c9c0cebdb694

import Mathlib.Topology.Order
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightNhds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The strict reflected drawdown ruin clock equals its countable schedule clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (a : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
      (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ, if X.X (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω -
          runningSup X (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω < -a
        then ((((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞) else ⊤) := by
  classical
  have hRight : ∀ s : ℝ≥0, X.X s ω - runningSup X s ω < -a →
      ∃ u : ℝ≥0, s < u ∧
        ∀ r : ℝ≥0, s ≤ r → r < u →
          X.X r ω - runningSup X r ω < -a := by
    intro s hs
    have hcont : ContinuousWithinAt
        (fun t : ℝ≥0 => X.X t ω - runningSup X t ω)
        (Ici s) s :=
      (X.rightCont ω s).sub
        ((runningSup_continuous_actual X ω).continuousWithinAt)
    have hev_ge : ∀ᶠ r in 𝓝[≥] s,
        X.X r ω - runningSup X r ω < -a :=
      hcont.tendsto.eventually (Iio_mem_nhds hs)
    have hev_gt : ∀ᶠ r in 𝓝[>] s,
        X.X r ω - runningSup X r ω < -a :=
      hev_ge.filter_mono (nhdsWithin_mono s Ioi_subset_Ici_self)
    rcases mem_nhdsGT_iff_exists_Ioo_subset.mp
        (show {r : ℝ≥0 | X.X r ω - runningSup X r ω < -a} ∈
          𝓝[>] s from hev_gt) with ⟨u, hsu, hu⟩
    refine ⟨u, hsu, ?_⟩
    intro r hsr hru
    rcases eq_or_lt_of_le hsr with heq | hlt
    · simpa [heq] using hs
    · exact hu ⟨hlt, hru⟩
  exact rightInterval_lower_strictExit_eq_schedule
    (fun t : ℝ≥0 => X.X t ω - runningSup X t ω) (-a) hRight
