-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_actual_BV_C1_any_strict_interior_band_ruin_stopped_compensator_integrable_mean_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:27:13.194794+00:00
-- url     : https://prove2.me/submissions/36113ba3-7630-4de4-bba9-e3416bdb0e1c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
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
    (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b)
    (hinside : Icc (a / 2) b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C}) :
    let E : Set (ℝ≥0 × Ω) := {p |
      ((p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C) ∧
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
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
  intro E G
  have hband : a / 2 ≤ b := by linarith
  obtain ⟨L, hLip⟩ :=
    avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
      X hBV C w hw_smooth (a / 2) b hband hinside
  have hbnonneg : 0 ≤ b := le_trans (le_of_lt ha) hab
  obtain ⟨R, hR, hBound⟩ :=
    avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
      w hw_cont hw_neg b hbnonneg
  have hCap : Icc a b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} := by
    intro y hy
    apply hinside
    exact ⟨(by linarith [hy.1,ha]), hy.2⟩
  have hMass : X.ν (Iic (-a / 2)) < ⊤ :=
    avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
      X a ha ha2
  exact avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
    X hBV T C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
    q x hq D hD a b (L : ℝ) R ha ha2 hab
    (NNReal.coe_nonneg L) hR hLip hBound hCap hMass
