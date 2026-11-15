-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24x2_ruinclipped_true_physical_precontact_signed_cash_HJB_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:49:14.808594+00:00
-- url     : https://prove2.me/submissions/94ad1213-dca3-493f-a2a4-09890d9b6576

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
import Theorems.Thm_AvramDividend_Classical_avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (active : ℕ → Bool)
    (hInterior : ∀ i ∈ Finset.range m, active i = true →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      let z := riskProcess X x D (v i) ω
      0 < z ∧ ENNReal.ofReal z < C)
    (hTimes : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v i ≤ v (i + 1))
    (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (hCellPre : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v (i+1) = 0 ∨ (v (i+1) : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let H : ℝ := ∑ i ∈ Finset.range m, if active i then
      Real.exp (-(q * (v i : ℝ))) *
        ((v (i+1) : ℝ) - (v i : ℝ)) *
        (X.generator w (riskProcess X x D (v i) ω) -
          q * w (riskProcess X x D (v i) ω)) else 0
    let J : ℝ := ∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
         w (riskProcess X x D u ω - (rightLimit D u ω - D u ω))))
    let Cash : ℝ := ∑ i ∈ Finset.range m,
      (      (∫⁻ t in Ioc (v i : ℝ) (v (i+1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i+1) : ℝ))) *
        (V (x + X.X (v (i+1)) ω - rightLimit D (v (i+1)) ω) -
         V (x + X.X (v (i+1)) ω - rightLimit D (v i) ω)))
    let Err : ℝ := ∑ i ∈ Finset.range m,
      (Real.exp (-(q * (v i : ℝ))) -
       Real.exp (-(q * (v (i+1) : ℝ)))) *
        (V (x + X.X (v (i+1)) ω - rightLimit D (v i) ω) -
         V (x + X.X (v (i+1)) ω - rightLimit D (v (i+1)) ω))
    H + J + Cash ≤ Err := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
  let V : ℝ → ℝ := fun z => if C = ⊤ then w z else
    if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  let H : ℝ := ∑ i ∈ Finset.range m, if active i then
    Real.exp (-(q * (v i : ℝ))) *
      ((v (i + 1) : ℝ) - (v i : ℝ)) *
      (X.generator w (riskProcess X x D (v i) ω) -
        q * w (riskProcess X x D (v i) ω)) else 0
  let J : ℝ := ∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
    ((rightLimit D u ω - D u ω) -
      (w (riskProcess X x D u ω) -
        w (riskProcess X x D u ω - (rightLimit D u ω - D u ω))))
  let Cash : ℝ := ∑ i ∈ Finset.range m,
    ((∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       Real.exp (-(q * (v (i + 1) : ℝ))) *
       (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
        V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))
  let Err : ℝ := ∑ i ∈ Finset.range m,
    (Real.exp (-(q * (v i : ℝ))) - Real.exp (-(q * (v (i + 1) : ℝ)))) *
      (V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
       V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω))
  change H + J + Cash ≤ Err
  have hHJ : H + J ≤ 0 := by
    exact avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
      X q hq w C hC hw_gen x D hjump σ n m ω
      active hInterior hTimes R hPre
  have hCash : Cash ≤ Err := by
    dsimp only [Cash, Err]; apply Finset.sum_le_sum
    intro i hi
    exact avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
      X x q (le_of_lt hq) C hC w hw_cont hw_smooth hw_grad D hD
      ω (v i) (v (i + 1)) (hTimes i hi) (hCellPre i hi)
  linarith
