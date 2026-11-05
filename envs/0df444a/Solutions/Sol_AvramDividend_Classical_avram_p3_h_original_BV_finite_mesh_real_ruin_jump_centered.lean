-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_real_ruin_jump_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:33:07.060782+00:00
-- url     : https://prove2.me/submissions/9094b027-773f-44a4-abd1-f7c9c5554ad9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_ruin_compensator_P3_E_G
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One uniform true original ruin-stopped compensated jump budget for a
finite nonempty family of strictly interior source reserve states. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (S : Finset ℝ) (hS : S.Nonempty)
    (hInside : ∀ z ∈ S, 0 < z ∧ ENNReal.ofReal z < C)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧
      (∀ z ∈ S, z ∈ Icc a b) ∧
      let τ : Ω → ℝ≥0 := fun ω =>
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
             w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
      Integrable (fun ω =>
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal))) P ∧
      (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal))) ∂P) = 0  := by
  obtain ⟨a, b, L, R, ha, ha2, hab, hCover, hL, hR, hLip, hWbound⟩ :=
    avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
      X hBV C w hwCont hwNeg hwC1 S hS hInside
  refine ⟨a, b, ha, ha2, hab, hCover, ?_⟩
  exact avram_p3_bv_original_real_ruin_compensator_P3_E_G
    X hBV x D hD w hwCont hwNeg q hq T a b L R
    ha ha2 hab hL hR hLip hWbound
