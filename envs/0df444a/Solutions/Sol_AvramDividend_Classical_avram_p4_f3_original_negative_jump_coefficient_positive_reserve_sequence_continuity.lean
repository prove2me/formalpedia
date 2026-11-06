-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_jump_coefficient_positive_reserve_sequence_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:30:52.623204+00:00
-- url     : https://prove2.me/submissions/6e007ad2-01e2-4ca3-b954-4985fe2cbe5a

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology

/-- Original negative-jump coefficients converge at positive pre- and postjump reserve states. -/
theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (u z : ℝ) (hu : 0 < u) (huz : 0 < u + z)
    (U : ℕ → ℝ) (hU : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun k => w (U k + z) - w (U k)) atTop
      (𝓝 (w (u + z) - w u)) := by
  have hPositiveCont (a : ℝ) (ha : 0 < a) :
      ContinuousAt w a := by
    apply hw_cont.continuousAt
    exact Filter.mem_of_superset (Ioi_mem_nhds ha)
      (by
        intro y hy
        change 0 < y at hy
        change 0 ≤ y
        exact le_of_lt hy)
  have hShift : Tendsto (fun k => U k + z) atTop (𝓝 (u + z)) :=
    hU.add tendsto_const_nhds
  exact ((hPositiveCont (u + z) huz).tendsto.comp hShift).sub
    ((hPositiveCont u hu).tendsto.comp hU)
