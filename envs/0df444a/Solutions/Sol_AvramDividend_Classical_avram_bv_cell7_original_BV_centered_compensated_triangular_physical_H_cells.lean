-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_centered_compensated_triangular_physical_H_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:46:16.026224+00:00
-- url     : https://prove2.me/submissions/5ea45351-c889-4cd0-92f1-ad3e4e70477b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_triangular_grid_compensator_L1_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_triangular_clock_indexed_H_exact_physical_cells

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The centred original triangular BV compensator and physical jump cells
    are simultaneously certified on the same original prefix clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (v : ℕ → ℕ → ℝ≥0) :
    (let M : ℕ → ℝ≥0 → Ω → ℝ := fun n S ω =>
      let τ : Ω → ℝ≥0 := fun ω' =>
        (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
             w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
        ((Measure.count.restrict
          {r : ℝ≥0 | 0 < r ∧
            X.X r ω' - Function.leftLim (fun z : ℝ≥0 => X.X z ω') r ≠ 0}).map
          (fun r : ℝ≥0 => (r,
            X.X r ω' - Function.leftLim (fun z : ℝ≥0 => X.X z ω') r)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
     let K : ℕ → Ω → ℝ := fun n ω =>
       Finset.sum (Finset.range (n + 1))
         (fun i => M n (v n (i + 1)) ω - M n (v n i) ω)
     ∀ n, Integrable (K n) P ∧ (∫ ω, K n ω ∂P) = 0) ∧
    (∀ᵐ ω ∂P, ∀ n i m : ℕ,
    let T : ℝ≥0 := v n i
    let τ : Ω → ℝ≥0 := fun η =>
      (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Eω : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
    let A : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then A p else 0)
    let Δ : ℝ≥0 → ℝ := fun z =>
      X.X z ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) z
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {z : ℝ≥0 | 0 < z ∧ Δ z ≠ 0}).map
        (fun z : ℝ≥0 => (z, Δ z)))
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
    let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (J p)
    let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then A p else 0))
    (∫ p, H ((p.1, ω), p.2) ∂NX) =
        (∑ j ∈ Finset.range (m + 1),
          ∑' z : ℝ≥0,
            if (0 < z ∧ Δ z ≠ 0) ∧ z ∈ Ioc (u j) (u (j + 1)) then
              Fp (z, Δ z) else 0).toReal -
        (∑ j ∈ Finset.range (m + 1),
          ∑' z : ℝ≥0,
            if (0 < z ∧ Δ z ≠ 0) ∧ z ∈ Ioc (u j) (u (j + 1)) then
              Fm (z, Δ z) else 0).toReal) := by
  constructor
  · exact
      AvramDividend.Classical.avram_bv_meas7_original_triangular_grid_compensator_L1_centered
        X hBV x C D hD w hw_cont hw_neg hwC1 q hq hw_gen
          a b ha ha2 hab hBand v
  · exact
      AvramDividend.Classical.avram_bv_cell7_original_BV_triangular_clock_indexed_H_exact_physical_cells
        X hBV x C D hD w hw_cont hw_neg hwC1 q hq
          a b ha hab hBand v
