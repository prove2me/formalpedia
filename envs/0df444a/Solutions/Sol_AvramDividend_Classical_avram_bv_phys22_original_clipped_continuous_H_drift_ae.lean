-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys22_original_clipped_continuous_H_drift_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T20:12:16.617444+00:00
-- url     : https://prove2.me/submissions/55ac52cb-1622-4c56-88d6-2bbe918db44a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) (m : ℕ) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let z : ℕ → ℝ := fun i =>
        x + X.X (u i) ω - rightLimit D (u i) ω
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      (∑ i ∈ Finset.range (m + 1),
        e i * (deriv w (z i) * (Y (u (i + 1)) - Y (u i)))) =
      (∑ i ∈ Finset.range (m + 1),
        e i * (deriv w (z i) *
          (X.drift * ((u (i + 1) : ℝ) - (u i : ℝ))))) := by
  have hraw :=
    avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  filter_upwards [hraw] with ω hω
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  let z : ℕ → ℝ := fun i =>
    x + X.X (u i) ω - rightLimit D (u i) ω
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  have hY (t : ℝ≥0) : Y t = (t : ℝ) * X.drift := by
    have ht := hω t
    change X.X t ω +
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0) = (t : ℝ) * X.drift
    linarith only [ht]
  change (∑ i ∈ Finset.range (m + 1),
      e i * (deriv w (z i) * (Y (u (i + 1)) - Y (u i)))) =
    (∑ i ∈ Finset.range (m + 1),
      e i * (deriv w (z i) *
        (X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)))))
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hY]
  ring
