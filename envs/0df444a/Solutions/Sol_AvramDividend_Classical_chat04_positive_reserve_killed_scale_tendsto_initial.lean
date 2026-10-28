-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_killed_scale_tendsto_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:00:04.771203+00:00
-- url     : https://prove2.me/submissions/bb9e99c7-43fc-4915-bfe8-5489933b8d67

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_discounted_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_unmasked_near_zero
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- A positive-reserve, history-killed discounted q-scale payoff tends
pathwise to its initial scale value as time approaches zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) (ω : Ω) :
    Filter.Tendsto
      (fun t : ℝ≥0 =>
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω)
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) := by
  have hraw :=
    chat04_positive_reserve_discounted_scale_tendsto_initial
      X q W hW x hx ω
  have hconv :
      Tendsto (fun t : ℝ≥0 =>
        ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)))
        (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hraw
  obtain ⟨ε, hε, hunmask⟩ :=
    chat04_positive_reserve_killed_scale_unmasked_near_zero X x q hx W ω
  have hevent :
      (fun t : ℝ≥0 =>
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω)
      =ᶠ[𝓝 (0 : ℝ≥0)]
      (fun t : ℝ≥0 =>
        ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) := by
    filter_upwards [Iio_mem_nhds hε] with t ht
    exact hunmask t ht
  exact hconv.congr' hevent.symm
