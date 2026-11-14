-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_C1_any_cofinal_row_true_ruin_compensator_integrable_mean_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:00:31.474894+00:00
-- url     : https://prove2.me/submissions/aa386727-e5da-442b-8f73-c7c7f90f1719

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_any_interior_C1_band_automatic_negative_mark_compensator_analytic_certificate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (hq : 0 ≤ q) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C}) :
    ∀ n : ℕ,
    let E : Set (ℝ≥0 × Ω) := {p |
      ((p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C) ∧
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by
  intro n E G
  obtain ⟨L, R, hL, hR, hLip, hBound, hMass⟩ :=
    avram_bva_a22_original_any_interior_C1_band_automatic_negative_mark_compensator_analytic_certificate
      X hBV C w hw_cont hw_neg hw_smooth (a n) (b n)
      (ha n) (ha2 n) (hab n) (hinside n)
  have hCap : Icc (a n) (b n) ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} := by
    intro y hy
    apply hinside n
    exact ⟨by linarith [hy.1, ha n], hy.2⟩
  exact avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
    X hBV T C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
    q x hq D hD (a n) (b n) L R (ha n) (ha2 n)
    (hab n) hL hR hLip hBound hCap hMass
