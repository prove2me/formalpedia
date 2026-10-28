-- Prove2me | solution 1 for AvramDividend.Classical.left_jump_magnitude_gt_add_continuous_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:04:03.938994+00:00
-- url     : https://prove2.me/submissions/0634575a-92f5-47e5-b3c1-14c280350d34

import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    (f g : ℝ≥0 → ℝ) (t : ℝ≥0) (hg : ContinuousAt g t) (r : ℝ) :
    (∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l) ∧
      r < l - f t) ↔
    (∃ l : ℝ, Tendsto (fun s => f s + g s)
      (nhdsWithin t (Iio t)) (nhds l) ∧
      r < l - (f t + g t)) := by
  have hgc : Tendsto g (nhdsWithin t (Iio t)) (nhds (g t)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · rintro ⟨l, hf, hmag⟩
    refine ⟨l + g t, hf.add hgc, ?_⟩
    have heq : l + g t - (f t + g t) = l - f t := by ring
    rwa [heq]
  · rintro ⟨l, hfg, hmag⟩
    have hf : Tendsto (fun s => (f s + g s) - g s)
        (nhdsWithin t (Iio t)) (nhds (l - g t)) :=
      hfg.sub hgc
    have heq : (fun s => (f s + g s) - g s) = f := by
      funext s
      simp
    rw [heq] at hf
    refine ⟨l - g t, hf, ?_⟩
    have heq' : (l - g t) - f t = l - (f t + g t) := by ring
    rwa [heq']