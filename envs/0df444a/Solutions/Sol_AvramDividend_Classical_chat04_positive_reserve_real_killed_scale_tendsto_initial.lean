-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_real_killed_scale_tendsto_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:29:33.664671+00:00
-- url     : https://prove2.me/submissions/5c91a25b-dd57-4eca-b885-a6b67de473e3

import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_discounted_scale_tendsto_initial
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

/-- Real-valued killed q-scale reward is initially continuous at every
strictly positive reserve, since the killing indicator is locally one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) (ω : Ω) :
    Filter.Tendsto
      (fun t : ℝ≥0 =>
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω)
      (𝓝 0) (𝓝 (W x)) := by
  obtain ⟨ε, hε, hsafe⟩ :=
    chat04_initial_safe_window_of_rightCont_zero X x hx ω (X.X_zero ω)
  have heq :
      (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) =ᶠ[𝓝 0]
      (fun t : ℝ≥0 =>
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω) := by
    filter_upwards [eventually_lt_nhds hε] with t ht
    symm
    have hm : ω ∈ {u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u} := by
      intro s hs
      have hs' := hsafe s (lt_of_le_of_lt hs ht)
      linarith
    exact Set.indicator_of_mem hm _
  exact (chat04_positive_reserve_discounted_scale_tendsto_initial
    X q W hW x hx ω).congr' heq