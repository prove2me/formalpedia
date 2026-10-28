-- Prove2me | solution 1 for AvramDividend.Classical.reflected_no_downward_jumps_of_continuous_supremum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:59:37.302658+00:00
-- url     : https://prove2.me/submissions/4e1a3834-86d8-4f48-adb0-1d45f0c5b548

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : ℝ≥0 → ℝ)
    (hS : ∀ t : ℝ≥0, ContinuousAt S t) :
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Filter.Tendsto (fun s : ℝ≥0 => S s - X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) →
      l ≤ S t - X.X t ω := by
  intro t l ht hR
  obtain ⟨lx, hXleft⟩ := X.leftLim ω t ht
  have hSleft : Tendsto S (nhdsWithin t (Iio t)) (nhds (S t)) :=
    (hS t).tendsto.mono_left nhdsWithin_le_nhds
  have hRleft : Tendsto
      (fun s : ℝ≥0 => S s - X.X s ω)
      (nhdsWithin t (Iio t)) (nhds (S t - lx)) :=
    hSleft.sub hXleft
  haveI : NeBot (nhdsWithin t (Iio t)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hl : l = S t - lx := tendsto_nhds_unique hR hRleft
  rw [hl]
  exact sub_le_sub_left (X.noPosJumps ω t lx ht hXleft) (S t)
