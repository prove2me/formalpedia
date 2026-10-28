-- Prove2me | solution 1 for AvramDividend.Classical.ennreal_bounded_right_continuity_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:05:04.807369+00:00
-- url     : https://prove2.me/submissions/0c7138ec-446c-486d-bff1-7fb67d9990f1

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.BoundedOrder.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Topology Set
open scoped ENNReal

theorem solution
    (F : ℝ → ℝ≥0∞)
    (hright : ∀ x : ℝ, ContinuousWithinAt F (Ici x) x)
    (hbound : ∀ x : ℝ, F x ≤ 1) :
    ∀ x : ℝ,
      ContinuousWithinAt (fun y : ℝ => (F y).toReal) (Ici x) x := by
  intro x
  have hne : F x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hbound x)
  exact (ENNReal.continuousAt_toReal hne).comp_continuousWithinAt
    (hright x)
