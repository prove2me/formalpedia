-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:45:25.437709+00:00
-- url     : https://prove2.me/submissions/be051f11-7c10-47eb-afcc-2941559c800e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_mark_rate_left_continuous_on_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original discounted marked compensator has the needed left continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) (q : ℝ) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r
    let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ContinuousWithinAt
      (fun r : ℝ≥0 => Real.exp (-(q * (r : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν)
      (Ioc 0 t ∩ U ⁻¹' A) t := by
  dsimp only
  intro hcap
  have hrate := avram_bvb_b20_original_mark_rate_left_continuous_on_cap
    X x C D hD ω S t ht htpos hsource hFinite w hw_cont hw_neg
    hw_meas hActivity hνatom hcap
  have hdiscount : ContinuousAt
      (fun r : ℝ≥0 => Real.exp (-(q * (r : ℝ)))) t := by
    fun_prop
  exact hdiscount.continuousWithinAt.mul hrate
