-- Prove2me | solution 1 for AvramDividend.Classical.chat04_zero_reserve_killed_renewal_of_positive_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:09:23.765181+00:00
-- url     : https://prove2.me/submissions/a0360b70-be6e-4ec6-a599-e1caf01a8aeb

import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_monotone_initial_capital
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.OrderClosed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Positive-reserve killed harmonicity extends to zero by monotone domination
    and continuity of the q-scale function, without pathwise zero regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (t : ℝ≥0)
    (hpositive : ∀ (x : ℝ), 0 < x →
      (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
        ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (X.X t u))) ω ∂P) =
      ENNReal.ofReal (W 0) := by
  let A : ℝ≥0∞ := ∫⁻ ω,
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s u}).indicator
      (fun u => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (X.X t u))) ω ∂P
  have hbound (a : ℝ) (ha : 0 < a) : A ≤ ENNReal.ofReal (W a) := by
    calc
      A ≤ (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ a + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (a + X.X t u))) ω ∂P) := by
          apply lintegral_mono
          intro ω
          simpa only [A, zero_add] using
            (chat04_killed_scale_payoff_monotone_initial_capital
              X q W hW 0 a (le_of_lt ha) t ω)
      _ = ENNReal.ofReal (W a) := hpositive a ha
  have hWzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hWlim : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 (W 0)) :=
    (hW.2.2.1.continuousWithinAt (by simp)).mono Ioi_subset_Ici_self
  have hlim : Tendsto (fun a : ℝ => ENNReal.ofReal (W a))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have he := (ENNReal.continuous_ofReal.tendsto (W 0)).comp hWlim
    simpa only [Function.comp_def, hWzero, ENNReal.ofReal_zero] using he
  have hA : A ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact hbound a ha
  have hA0 : A = 0 := le_antisymm hA bot_le
  simpa only [A, hWzero, ENNReal.ofReal_zero] using hA0
