-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian13_actual_random_interval_bracket_L1_of_mean_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:37:41.941792+00:00
-- url     : https://prove2.me/submissions/656c5c00-a2f7-44f4-9aea-a5320e832455

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_actual_masked_random_interval_bracket_le_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Integrable physical random-clock mass controls the true stopped Gaussian
square bracket in L¹, with measurability as the explicit remaining interface. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μtime : Measure ℝ≥0) (s t : Ω → ℝ≥0)
    (hFinite : ∀ ω, μtime (Ioc (s ω) (t ω)) < ⊤)
    (hMassI : Integrable (fun ω =>
      (μtime.restrict (Ioc (s ω) (t ω))).real Set.univ) P) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    AEStronglyMeasurable (fun ω =>
      ∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) P →
    Integrable (fun ω =>
      ∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) P := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  obtain ⟨K, hK, hBound⟩ :=
    avram_ubv_gaussian13_actual_masked_random_interval_bracket_le_mass
      X x D hD w a b u v hw hau huv hvb μtime s t hFinite
  change AEStronglyMeasurable (fun ω =>
    ∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) P →
    Integrable (fun ω =>
      ∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) P
  intro hMeas
  have hDom : Integrable (fun ω => K ^ 2 *
      (μtime.restrict (Ioc (s ω) (t ω))).real Set.univ) P := by
    simpa using hMassI.const_mul (K ^ 2)
  apply hDom.mono' hMeas
  filter_upwards [] with ω
  have hNonneg : 0 ≤ ∫ r in Ioc (s ω) (t ω),
      (G (r, ω)) ^ 2 ∂μtime :=
    integral_nonneg (fun r => sq_nonneg (G (r, ω)))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hNonneg] using hBound ω
