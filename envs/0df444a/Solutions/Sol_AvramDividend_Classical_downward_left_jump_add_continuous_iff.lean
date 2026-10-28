-- Prove2me | solution 1 for AvramDividend.Classical.downward_left_jump_add_continuous_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:06:35.760204+00:00
-- url     : https://prove2.me/submissions/c49b192f-fccb-4faa-ba68-9ab8df9bb8b9

import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    (f g : ℝ≥0 → ℝ) (t : ℝ≥0) (hg : ContinuousAt g t) :
    (∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l) ∧ f t < l) ↔
    (∃ l : ℝ, Tendsto (fun s => f s + g s)
      (nhdsWithin t (Iio t)) (nhds l) ∧ f t + g t < l) := by
  have hgc : Tendsto g (nhdsWithin t (Iio t)) (nhds (g t)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · rintro ⟨l, hf, hlt⟩
    refine ⟨l + g t, hf.add hgc, ?_⟩
    simpa only [add_comm (g t)] using (add_lt_add_right hlt (g t))
  · rintro ⟨l, hfg, hlt⟩
    have hf : Tendsto (fun s => (f s + g s) - g s)
        (nhdsWithin t (Iio t)) (nhds (l - g t)) :=
      hfg.sub hgc
    have heq : (fun s => (f s + g s) - g s) = f := by
      funext s
      simp
    rw [heq] at hf
    exact ⟨l - g t, hf, (lt_sub_iff_add_lt).mpr hlt⟩