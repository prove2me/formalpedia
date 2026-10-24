-- Prove2me | solution 1 for AvramDividend.Classical.chat04_survived_strip_scale_lintegral_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:51:37.458208+00:00
-- url     : https://prove2.me/submissions/1bbf1185-c15e-4d3c-929d-d0a23c3626dc

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_bounded_strip_scale_terminal_vanish
import Theorems.Thm_AvramDividend_Classical_chat04_survived_strip_scale_tail_lintegral_bound
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

/-- Vanishing expected killed q-scale terminal residual at integer horizons. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ =>
      (∫⁻ ω, if (∀ s : ℝ≥0, s ≤ (n : ℝ≥0) →
             0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a) then
         ENNReal.ofReal (Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω))
        else 0 ∂P)) atTop (𝓝 (0 : ENNReal)) := by
  have hreal : Tendsto
      (fun n : ℕ => Real.exp (-(q * (n : ℝ))) * W a) atTop (𝓝 (0 : ℝ)) := by
    apply chat04_bounded_strip_scale_terminal_vanish X q hq W hW a (fun _ => a)
    intro n
    exact ⟨ha, le_rfl⟩
  have hupper : Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.exp (-(q * (n : ℝ))) * W a))
      atTop (𝓝 (0 : ENNReal)) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hbound : ∀ n : ℕ,
      (∫⁻ ω, if (∀ s : ℝ≥0, s ≤ (n : ℝ≥0) →
             0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a) then
         ENNReal.ofReal (Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω))
        else 0 ∂P) ≤
       ENNReal.ofReal (Real.exp (-(q * (n : ℝ))) * W a) := by
    intro n
    exact chat04_survived_strip_scale_tail_lintegral_bound
      X q hq W hW a x (n : ℝ≥0) (n : ℝ≥0) le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ => bot_le) hbound
