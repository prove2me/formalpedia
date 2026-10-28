-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_zero_of_early_downward_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:51:15.199366+00:00
-- url     : https://prove2.me/submissions/e4b37e3e-e6ae-4b95-bc0c-2d1608ad533c

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_path_decrease
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Downward jumps arbitrarily close to zero produce strict decreases before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hJumps : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω) (nhdsWithin t (Iio t)) (nhds l) ∧
          X.X t ω < l) :
    barrierRuinTime X 0 ω = 0 := by
  apply barrierRuinTime_zero_of_near_zero_path_decrease X ω
  intro ε hε
  obtain ⟨t, ht0, htε, l, hleft, hdown⟩ := hJumps ε hε
  letI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
  have hearlier : ∀ᶠ s : ℝ≥0 in nhdsWithin t (Iio t), s < t := self_mem_nhdsWithin
  have habove : ∀ᶠ s : ℝ≥0 in nhdsWithin t (Iio t), X.X t ω < X.X s ω :=
    hleft.eventually_const_lt hdown
  obtain ⟨s, hst, hdrop⟩ := (hearlier.and habove).exists
  exact ⟨s, t, le_of_lt hst, htε, hdrop⟩
