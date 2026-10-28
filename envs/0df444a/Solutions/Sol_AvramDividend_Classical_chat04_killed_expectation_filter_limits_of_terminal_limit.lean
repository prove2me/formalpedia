-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_expectation_filter_limits_of_terminal_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:47:18.59583+00:00
-- url     : https://prove2.me/submissions/93b27d3e-7fca-49fb-bf86-82035986b247

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_expectation_filter_fatou
import Theorems.Thm_AvramDividend_Classical_chat04_killed_expectation_limsup_le_of_terminal_limit
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Both killed q-scale expectation filter limits agree with the initial
reserve value whenever terminal-only expectation continuity is known. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x)
    (hterminal : Tendsto (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | 0 ≤ x + X.X t u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P))
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x)))) :
    Filter.liminf (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)) (𝓝 0) =
      ENNReal.ofReal (W x) ∧
    Filter.limsup (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)) (𝓝 0) =
      ENNReal.ofReal (W x) := by
  let f : ℝ≥0 → ENNReal := fun t => (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
  have hlo : ENNReal.ofReal (W x) ≤ Filter.liminf f (𝓝 0) := by
    simpa only [f] using
      (chat04_positive_reserve_killed_expectation_filter_fatou
        X q W hW x hx)
  have hhi : Filter.limsup f (𝓝 0) ≤ ENNReal.ofReal (W x) := by
    simpa only [f] using
      (chat04_killed_expectation_limsup_le_of_terminal_limit
        X q W hW x hterminal)
  have hbetween :
      Filter.liminf f (𝓝 0) ≤ Filter.limsup f (𝓝 0) :=
    Filter.liminf_le_limsup
  have h1 : Filter.liminf f (𝓝 0) = ENNReal.ofReal (W x) :=
    le_antisymm (hbetween.trans hhi) hlo
  have h2 : Filter.limsup f (𝓝 0) = ENNReal.ofReal (W x) :=
    le_antisymm hhi (hlo.trans hbetween)
  exact ⟨h1, h2⟩
