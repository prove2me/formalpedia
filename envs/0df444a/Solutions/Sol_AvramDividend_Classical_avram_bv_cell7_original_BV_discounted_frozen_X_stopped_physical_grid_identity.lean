-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_frozen_X_stopped_physical_grid_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:32:47.212016+00:00
-- url     : https://prove2.me/submissions/2c3e979e-26fb-4f91-b3e8-27937c65be26

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The four original BV C1 drift, aggregate jump, cross and Taylor terms
    combine to the actual discounted frozen-dividend value increment on each
    ruin/horizon clipped physical cell, including the final contact cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let frozen : ℕ → ℝ := fun i =>
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let rem : ℕ → ℝ := fun i =>
      cash i + e i * (post (i + 1) - post i - frozen i)
    rightLimit D 0 ω +
      ((∑ i ∈ Finset.range (m + 1), cash i) +
        e (m + 1) * post (m + 1) - e 0 * post 0) =
      rightLimit D 0 ω +
      ((∑ i ∈ Finset.range (m + 1), e i * frozen i) +
       (∑ i ∈ Finset.range (m + 1),
         (e (i + 1) - e i) * post (i + 1)) +
       (∑ i ∈ Finset.range (m + 1), rem i)) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  let z : ℕ → ℝ := fun i => x + X.X (u i) ω - rightLimit D (u i) ω
  let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
  let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  let frozen : ℕ → ℝ := fun i =>
    w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
  have hcell (i : ℕ) :
      e i * (deriv w (z i) * c i) +
      e i * (w (z i - j i) - w (z i)) +
      e i * (w (z i + c i - j i) - w (z i + c i) -
        w (z i - j i) + w (z i)) +
      e i * (w (z i + c i) - w (z i) - deriv w (z i) * c i) =
      e i * frozen i := by
    have hz : z i + c i - j i =
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω := by
      dsimp [z, c, j, Y]
      ring
    have hf : frozen i = w (z i + c i - j i) - w (z i) := by
      rw [hz]
    rw [hf]
    ring
  have hsum :
      (∑ i ∈ Finset.range (m + 1),
        (e i * (deriv w (z i) * c i) +
         e i * (w (z i - j i) - w (z i)) +
         e i * (w (z i + c i - j i) - w (z i + c i) -
           w (z i - j i) + w (z i)) +
         e i * (w (z i + c i) - w (z i) - deriv w (z i) * c i))) =
      (∑ i ∈ Finset.range (m + 1), e i * frozen i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hcell i
  simp only [Finset.sum_add_distrib] at hsum
  have hraw :=
    AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity
      X hBV x C D hD w q ω T m
  dsimp only at hraw ⊢
  rw [hraw]
  dsimp only [τ, u, J, Y, z, c, j, e, frozen] at hsum
  linarith
