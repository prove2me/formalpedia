-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_original_cofinal_band_uniform_compensated_M
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:41:17.653601+00:00
-- url     : https://prove2.me/submissions/a878fc8d-5c2f-470e-982e-ca2ab55162d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_allcap_full_mask_total_jump_centered_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_given_uniform_grid_centred_compensator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) ∧
      ∀ n : ℕ,
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
            {v : ℝ≥0 | 0 < v ∧
              X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map
            (fun v : ℝ≥0 => (v,
              X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      Integrable (fun ω => Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω)) P ∧
      (∫ ω, Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω) ∂P) = 0 := by
  obtain ⟨a, b, ha, ha2, hab, hBand, hCof, _v, _hv0, _hvEnd, _hvMono, _hvWidth, _hvCells⟩ :=
    avram_bv_meas7_original_allcap_full_mask_total_jump_centered_predictable
      X hBV x C D hD hC w hw_cont hw_neg hw_smooth q
      (le_of_lt hq) hw_gen T hT
  have huWidth : ∀ n i, i < n + 1 →
      (u n (i + 1) : ℝ) - (u n i : ℝ) =
        T / ((n : ℝ) + 2) := by
    intro n i _
    rw [huniform n (i + 1), huniform n i]
    push_cast
    ring
  refine ⟨a, b, ha, ha2, hab, hBand, hCof, ?_⟩
  exact avram_p3_comp8_original_given_uniform_grid_centred_compensator
    X hBV x C D hD w hw_cont hw_neg hw_smooth q (le_of_lt hq)
    hw_gen a b ha ha2 hab hBand T hT u hu0 huWidth
