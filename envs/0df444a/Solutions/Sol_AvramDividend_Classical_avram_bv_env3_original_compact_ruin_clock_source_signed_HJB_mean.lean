-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_compact_ruin_clock_source_signed_HJB_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:49:58.870662+00:00
-- url     : https://prove2.me/submissions/c4d1ff35-4caa-4aee-93ed-a7327e9a4d39

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep10_original_C1_signed_HJB_from_admissible_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0) (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let Upre : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Upre p.1 + p.2) - w (Upre p.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let F : ℝ≥0 × Ω → ℝ := fun p =>
      if p ∈ E then
        Real.exp (-(q * (p.1 : ℝ))) *
          (X.drift * deriv w (Upre p) +
            (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
            q * w (Upre p))
      else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let M : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))
    let B : Ω → ℝ := fun ω =>
      ∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by
  classical
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let E : Set (ℝ≥0 × Ω) := {p |
    (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
  obtain ⟨hτBound, hτ, hEm, hEregion, hEwindow, ⟨L, R, hL, hR, hLip, hWbound⟩⟩ :=
    avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
      X hBV x C D hD w hw_cont hw_neg hw_smooth T a b ha hab hBand
  have hbC : ENNReal.ofReal b < C :=
    (hBand ⟨by nlinarith [ha, hab], le_refl b⟩).2
  have hEcap : ∀ p ∈ E, ENNReal.ofReal
      (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) < C := by
    intro p hp
    have hpab := hEregion p hp
    have hpwide : Function.leftLim
        (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈
        Icc (a / 2) b := ⟨by nlinarith [hpab.1, ha], hpab.2⟩
    exact (hBand hpwide).2
  simpa only using
    (avram_integration_sweep10_original_C1_signed_HJB_from_admissible_source
    X hBV T τ hτBound hτ x D hD.1.1 w hw_cont hw_neg q hq
    a b ha ha2 hab E hEm hEregion C hD hbC hw_smooth hw_gen hEcap)
