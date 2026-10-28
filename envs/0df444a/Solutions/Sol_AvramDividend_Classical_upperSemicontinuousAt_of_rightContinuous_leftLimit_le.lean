-- Prove2me | solution 1 for AvramDividend.Classical.upperSemicontinuousAt_of_rightContinuous_leftLimit_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:00:05.701159+00:00
-- url     : https://prove2.me/submissions/83302b7e-4fa2-4d76-9c38-f27d880edba5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.NhdsWithin
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hRight : ContinuousWithinAt f (Ici t) t)
    (l : ℝ)
    (hLeft : Filter.Tendsto f (nhdsWithin t (Iio t)) (nhds l))
    (hle : l ≤ f t) :
    UpperSemicontinuousAt f t := by
  apply upperSemicontinuousAt_iff.mpr
  intro y hy
  have hL : ∀ᶠ s in nhdsWithin t (Iio t), f s < y :=
    hLeft.eventually (isOpen_Iio.mem_nhds (lt_of_le_of_lt hle hy))
  have hR : ∀ᶠ s in nhdsWithin t (Ici t), f s < y :=
    hRight.eventually (isOpen_Iio.mem_nhds hy)
  have hFilt : nhds t =
      nhdsWithin t (Iio t) ⊔ nhdsWithin t (Ici t) := by
    simpa only [Set.Iio_union_Ici, nhdsWithin_univ] using
      (nhdsWithin_union t (Iio t) (Ici t))
  rw [hFilt]
  exact (Filter.eventually_sup).2 ⟨hL, hR⟩
