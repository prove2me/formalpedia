-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_turn13_original_two_scale_compensated_grid_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:26:11.746201+00:00
-- url     : https://prove2.me/submissions/7e048178-ec9b-45ef-af76-8c35841455bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_finite_physical_grid_increment_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (ha2 : ∀ k, a k ≤ 2)
    (hab : ∀ k, a k ≤ b k)
    (hBand : ∀ k, Icc (a k / 2) (b k) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (u : ℕ → ℕ → ℝ≥0) :
    let K : ℕ → ℕ → Ω → ℝ := fun n k ω =>
      let M : ℝ≥0 → Ω → ℝ := fun S ω' =>
        let τ : Ω → ℝ≥0 := fun ω'' =>
          (min (ruinTime X x D ω'') (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a k) (b k)}
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
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω'' =>
          ((Measure.count.restrict
            {v : ℝ≥0 | 0 < v ∧
              X.X v ω'' - Function.leftLim (fun z : ℝ≥0 => X.X z ω'') v ≠ 0}).map
            (fun v : ℝ≥0 => (v,
              X.X v ω'' - Function.leftLim (fun z : ℝ≥0 => X.X z ω'') v)))
        (∫ p, H ((p.1, ω'), p.2) ∂(NX ω')) -
        (∫ t, ∫ z, H ((t, ω'), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      Finset.sum (Finset.range (n + 1)) (fun i => M (u n (i + 1)) ω - M (u n i) ω)
    ∀ n k, Integrable (K n k) P ∧ (∫ ω, K n k ω ∂P) = 0 := by
  intro K n k
  exact avram_bv_meas7_original_finite_physical_grid_increment_centered
    X hBV x C D hD w hw_cont hw_neg hw_smooth q hq hw_gen
    a b ha ha2 hab hBand k (n + 1) (u n)
