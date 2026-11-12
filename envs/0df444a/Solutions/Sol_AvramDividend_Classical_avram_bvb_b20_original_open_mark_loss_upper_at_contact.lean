-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_original_open_mark_loss_upper_at_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:26:37.9148+00:00
-- url     : https://prove2.me/submissions/74b33fc7-6474-41c1-97db-7a51dd275e1a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_open_mask_local_upper_closed_mark_loss
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Source-exact local open-mask comparison, with the rate sign discharged. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) (q : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r
    let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ∀ᶠ r in 𝓝[Ioc 0 t ∩ U ⁻¹' A] t,
      (if 0 < U r ∧ ENNReal.ofReal (U r) < C then
        -(Real.exp (-(q * (r : ℝ))) *
          ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν)
       else 0) ≤
      -(Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν) + ε := by
  exact avram_bvb_b20_original_open_mask_local_upper_closed_mark_loss
    X x C D hD ω S t ht htpos hsource hFinite w hw_cont hw_neg
    hw_meas hActivity hνatom q
    (fun b hb hbc => avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad X.ν b hb hbc)
    ε hε
