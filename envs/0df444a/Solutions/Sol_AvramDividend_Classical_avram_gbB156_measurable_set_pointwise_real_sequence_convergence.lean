-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB156_measurable_set_pointwise_real_sequence_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:56:34.381847+00:00
-- url     : https://prove2.me/submissions/3d9fe9a7-f89b-41ed-91c4-c98fb3d1b028

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ m, Measurable (f m)) (hg : Measurable g) :
    MeasurableSet {z : α | Filter.Tendsto (fun m : ℕ => f m z) Filter.atTop (𝓝 (g z))} := by
  have hzero : MeasurableSet {z : α |
      Filter.Tendsto (fun m : ℕ => f m z - g z) Filter.atTop (𝓝 (0 : ℝ))} :=
    measurableSet_tendsto (𝓝 (0 : ℝ)) (fun m => (hf m).sub hg)
  have heq : {z : α |
      Filter.Tendsto (fun m : ℕ => f m z) Filter.atTop (𝓝 (g z))} =
      {z : α |
        Filter.Tendsto (fun m : ℕ => f m z - g z) Filter.atTop (𝓝 (0 : ℝ))} := by
    ext z
    constructor
    · intro h
      change Filter.Tendsto (fun m : ℕ => f m z) Filter.atTop (𝓝 (g z)) at h
      change Filter.Tendsto (fun m : ℕ => f m z - g z)
        Filter.atTop (𝓝 (0 : ℝ))
      have hc : Filter.Tendsto (fun _ : ℕ => g z) Filter.atTop (𝓝 (g z)) :=
        tendsto_const_nhds
      simpa only [sub_self] using h.sub hc
    · intro h
      change Filter.Tendsto (fun m : ℕ => f m z - g z)
        Filter.atTop (𝓝 (0 : ℝ)) at h
      change Filter.Tendsto (fun m : ℕ => f m z)
        Filter.atTop (𝓝 (g z))
      have hc : Filter.Tendsto (fun _ : ℕ => g z) Filter.atTop (𝓝 (g z)) :=
        tendsto_const_nhds
      have hsum := h.add hc
      have hfun : (fun m : ℕ => (f m z - g z) + g z) =
          (fun m : ℕ => f m z) := by
        funext m
        ring
      rw [hfun] at hsum
      simpa only [zero_add] using hsum
  rw [heq]
  exact hzero
