-- Prove2me | solution 1 for AvramDividend.Classical.bv_inverse_frequency_small_reserve_early_ruin_tendsto_zero_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:30:23.187114+00:00
-- url     : https://prove2.me/submissions/228b490c-1f3b-4806-a4c8-1f6b2c9e3b16

import Theorems.Thm_AvramDividend_Classical_bv_uniform_smalltime_drift_deficit_tails_tendsto_zero_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (δ : ℕ → ℝ≥0) (θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθge : ∀ n, 1 ≤ θ n)
    (hProduct : ∀ n, (δ n : ℝ) * θ n = c)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      P.real {ω : Ω | ∃ t : ℝ≥0, t ≤ δ n ∧
        a + θ n * X.X t ω < 0})
      atTop (𝓝 (0 : ℝ)) := by
  haveI := X.isProbability
  have hd : 0 ≤ X.drift := le_of_lt (bv_standing_drift_pos X hX hBV).1
  let A : ℕ → Set Ω := fun n =>
    {ω | ∃ t : ℝ≥0, t ≤ δ n ∧ a + θ n * X.X t ω < 0}
  let B : ℕ → Set Ω := fun n =>
    {ω | ∃ t : ℝ≥0, t ≤ δ n ∧
      a ≤ θ n * ((t : ℝ) * X.drift - X.X t ω)}
  have hBound : ∀ n, P.real (A n) ≤ P.real (B n) := by
    intro n
    have hSubset : A n ⊆ B n := by
      intro ω hω
      obtain ⟨t, ht, hneg⟩ := hω
      have hθnn : 0 ≤ θ n := le_trans (by norm_num : (0 : ℝ) ≤ 1) (hθge n)
      have ht0 : 0 ≤ (t : ℝ) := t.2
      have hnonneg : 0 ≤ θ n * ((t : ℝ) * X.drift) :=
        mul_nonneg hθnn (mul_nonneg ht0 hd)
      refine ⟨t, ht, ?_⟩
      nlinarith [hnonneg]
    have hMeasure : P (A n) ≤ P (B n) := measure_mono hSubset
    change (P (A n)).toReal ≤ (P (B n)).toReal
    exact ENNReal.toReal_mono (measure_ne_top P (B n)) hMeasure
  have hTarget : Tendsto (fun n => P.real (B n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [B] using
      bv_uniform_smalltime_drift_deficit_tails_tendsto_zero_ws01b
        X hBV δ θ c hθ hθge hProduct a ha
  have hLower : ∀ n, (0 : ℝ) ≤ P.real (A n) := by
    intro n
    exact measureReal_nonneg
  change Tendsto (fun n => P.real (A n)) atTop (𝓝 (0 : ℝ))
  exact Filter.Tendsto.squeeze tendsto_const_nhds hTarget hLower hBound
