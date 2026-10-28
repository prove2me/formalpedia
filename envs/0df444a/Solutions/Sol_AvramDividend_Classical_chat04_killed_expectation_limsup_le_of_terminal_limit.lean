-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_expectation_limsup_le_of_terminal_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:36:31.815313+00:00
-- url     : https://prove2.me/submissions/0d5aee04-ed6a-4d99-baed-9acc2e41af14

import Theorems.Thm_AvramDividend_Classical_chat01_history_killed_lintegral_le_terminal_only
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- The upper-semicontinuity half of the killed time-zero limit follows
from terminal-only convergence and genuine path-survival domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hterminal : Tendsto (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | 0 ≤ x + X.X t u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P))
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x)))) :
    Filter.limsup (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)) (𝓝 0) ≤
      ENNReal.ofReal (W x) := by
  let lower : ℝ≥0 → ENNReal := fun t => (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
  let upper : ℝ≥0 → ENNReal := fun t => (∫⁻ ω,
        ({u : Ω | 0 ≤ x + X.X t u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
  have hle (t : ℝ≥0) : lower t ≤ upper t := by
    simpa only [lower, upper] using
      (chat01_history_killed_lintegral_le_terminal_only X q W hW x t)
  have hu : Tendsto upper (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) := by
    simpa only [upper] using hterminal
  have hbound : Filter.limsup lower (𝓝 0) ≤ ENNReal.ofReal (W x) := by
    calc
      Filter.limsup lower (𝓝 0) ≤ Filter.limsup upper (𝓝 0) :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)
      _ = ENNReal.ofReal (W x) := hu.limsup_eq
  simpa only [lower] using hbound
