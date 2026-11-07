-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_allcap_original_finite_grid_compensated_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:51:58.911279+00:00
-- url     : https://prove2.me/submissions/13adabbc-f3fb-469c-a0c2-e654e82876e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_finite_physical_grid_increment_centered
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_allcap_expanding_compact_band_witnesses
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original stopped Levy compensated jumps have integrable centred
finite-grid increments at every positive cap via explicit compact bands. -/
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
    (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      ∀ (n k : ℕ) (u : ℕ → ℝ≥0),
    let M : ℝ≥0 → Ω → ℝ := fun S ω =>
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
          {u : ℝ≥0 | 0 < u ∧
            X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
    Integrable (fun ω => Finset.sum (Finset.range k)
      (fun i => M (u (i + 1)) ω - M (u i) ω)) P ∧
    (∫ ω, (Finset.sum (Finset.range k)
      (fun i => M (u (i + 1)) ω - M (u i) ω)) ∂P) = 0 := by
  obtain ⟨a, b, ha, ha2, hab, hBand⟩ :=
    avram_p3_grid4_allcap_expanding_compact_band_witnesses C hC
  refine ⟨a, b, ha, ha2, hab, hBand, ?_⟩
  intro n k u
  exact avram_bv_meas7_original_finite_physical_grid_increment_centered
    X hBV x C D hD w hw_cont hw_neg hw_smooth q hq hw_gen
    a b ha ha2 hab hBand n k u
