-- Prove2me | solution 1 for AvramDividend.Classical.bv_uniform_smalltime_drift_deficit_tails_tendsto_zero_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:21:59.242686+00:00
-- url     : https://prove2.me/submissions/2b6ed4c5-c6d3-4b54-8c5e-e5e7b4f01dcc

import Theorems.Thm_AvramDividend_Classical_bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Order.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (δ : ℕ → ℝ≥0) (θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθge : ∀ n, 1 ≤ θ n)
    (hProduct : ∀ n, (δ n : ℝ) * θ n = c)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      P.real {ω : Ω | ∃ t : ℝ≥0, t ≤ δ n ∧
        a ≤ θ n * ((t : ℝ) * X.drift - X.X t ω)})
      atTop (𝓝 (0 : ℝ)) := by
  haveI := X.isProbability
  let E : ℕ → Set Ω := fun n =>
    {ω | ∃ t : ℝ≥0, t ≤ δ n ∧
      a ≤ θ n * ((t : ℝ) * X.drift - X.X t ω)}
  let F : ℕ → Set Ω := fun n =>
    {ω | a ≤ θ n * ((δ n : ℝ) * X.drift - X.X (δ n) ω)}
  have hBound : ∀ n, P.real (E n) ≤ P.real (F n) := by
    intro n
    have hAe : ∀ᵐ ω ∂P, ω ∈ E n → ω ∈ F n := by
      filter_upwards [bv_drift_deficit_ae_monotone_all_times X hBV] with ω hmono hmem
      obtain ⟨t, ht, hlarge⟩ := hmem
      have hmono' :
          (t : ℝ) * X.drift - X.X t ω ≤
          (δ n : ℝ) * X.drift - X.X (δ n) ω := by
        simpa only [mul_comm X.drift (t : ℝ),
          mul_comm X.drift (δ n : ℝ)] using (hmono ht)
      exact le_trans hlarge
        (mul_le_mul_of_nonneg_left hmono' (by linarith [hθge n]))
    have hMeasure : P (E n) ≤ P (F n) := measure_mono_ae hAe
    change (P (E n)).toReal ≤ (P (F n)).toReal
    exact ENNReal.toReal_mono (measure_ne_top P (F n)) hMeasure
  have hZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have hTarget : Tendsto (fun n => P.real (F n)) atTop (𝓝 0) := by
    simpa only [F] using
      bv_scaled_drift_deficit_tails_tendsto_zero_ws01b X hBV δ θ c hθ hθge hProduct a ha
  have hLower : ∀ n, (0 : ℝ) ≤ P.real (E n) := by
    intro n
    exact measureReal_nonneg
  change Tendsto (fun n => P.real (E n)) atTop (𝓝 (0 : ℝ))
  exact Filter.Tendsto.squeeze hZero hTarget hLower hBound
