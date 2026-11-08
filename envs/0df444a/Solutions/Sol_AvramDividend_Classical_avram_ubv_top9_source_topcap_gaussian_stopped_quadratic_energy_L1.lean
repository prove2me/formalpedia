-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_source_topcap_gaussian_stopped_quadratic_energy_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:23:24.447503+00:00
-- url     : https://prove2.me/submissions/5490fa1f-94ed-4a9a-a7c6-4e3e81d221f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_original_predictable_gaussian_gradient_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_predictable_inclusive_sigma_mask_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original topcap Gaussian compact gradient has stopped physical quadratic energy in L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ a b B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (ha : 0 < a) (hau : a < u + δ) (hvb : v < b) (hb : b < B)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0
    Integrable (fun ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then (H (t, ω)) ^ 2 else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨μ, _, hμclock, _, _, hHm, hHenergy⟩ :=
    avram_ubv_loc6_topcap_original_predictable_gaussian_gradient_HJB_source
      X x D C hD hTop w hw_smooth hw_cont hw_neg q hw_gen hw_grad
      u v δ a b B hu hδ hδone huv hv ha hau hvb hb T
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
        ∈ Icc (u + δ) v
      then deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
      else 0
  have hH2 : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; Integrable (fun p => (H p) ^ 2) μ) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    have hMeas : AEStronglyMeasurable (fun p => (H p) ^ 2) μ :=
      (hHm.pow_const 2).aestronglyMeasurable
    refine ⟨hMeas, ?_⟩
    change (∫⁻ p : ℝ≥0 × Ω, ‖(H p) ^ 2‖ₑ ∂μ) < ⊤
    calc
      (∫⁻ p : ℝ≥0 × Ω, ‖(H p) ^ 2‖ₑ ∂μ) =
          ∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ := by
            apply lintegral_congr_ae
            filter_upwards [] with p
            exact Real.enorm_eq_ofReal (sq_nonneg (H p))
      _ < ⊤ := hHenergy
  exact avram_ubv_finite9_predictable_inclusive_sigma_mask_L1
    T μ hμclock (fun p => (H p) ^ 2) hH2 σ hσstop
