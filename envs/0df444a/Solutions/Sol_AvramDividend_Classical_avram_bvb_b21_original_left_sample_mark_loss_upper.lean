-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_left_sample_mark_loss_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:06:27.109491+00:00
-- url     : https://prove2.me/submissions/7767ac8c-5575-412e-906a-d91667c59026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_open_mark_loss_upper_at_contact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Unconditional left-sample upper bound for the original masked mark rate. -/
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
    (s : ℕ → ℝ≥0) (hs : Tendsto s atTop (𝓝 t))
    (hleft : ∀ᶠ n in atTop, 0 < s n ∧ s n ≤ t)
    (ε : ℝ) (hε : 0 < ε) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ∀ᶠ n in atTop,
      (if 0 < U (s n) ∧ ENNReal.ofReal (U (s n)) < C then
        -(Real.exp (-(q * (s n : ℝ))) *
          ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν)
       else 0) ≤
      -(Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν) + ε := by
  dsimp only
  intro hcap
  let U : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
  let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
  let H : ℝ≥0 → ℝ := fun r =>
    -(Real.exp (-(q * (r : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν)
  have hwithin : ∀ᶠ r in 𝓝[Ioc 0 t ∩ U ⁻¹' A] t,
      (if 0 < U r ∧ ENNReal.ofReal (U r) < C then H r else 0) ≤ H t + ε := by
    exact avram_bvb_b20_original_open_mark_loss_upper_at_contact
      X x C hC D hD ω S t ht htpos hsource hFinite
      w hw_cont hw0 hw_neg hw_meas hw_smooth hw_grad
      hActivity hνatom q ε hε hcap
  have hnear : ∀ᶠ r in 𝓝 t,
      r ∈ Ioc 0 t ∩ U ⁻¹' A →
        (if 0 < U r ∧ ENNReal.ofReal (U r) < C then H r else 0) ≤ H t + ε :=
    (eventually_nhdsWithin_iff).1 hwithin
  have hnonneg : 0 ≤ H t := by
    have hsign := avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad X.ν (U t) hcap.1 hcap.2
    have hexp := Real.exp_pos (-(q * (t : ℝ)))
    dsimp [H]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hexp.le hsign)
  filter_upwards [hs.eventually hnear, hleft] with n hn hsn
  change (if 0 < U (s n) ∧ ENNReal.ofReal (U (s n)) < C then
    H (s n) else 0) ≤ H t + ε
  by_cases hA : 0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C
  · exact hn ⟨hsn, hA⟩
  · have hout : ¬(0 < U (s n) ∧ ENNReal.ofReal (U (s n)) < C) := by
      intro h
      exact hA ⟨le_of_lt h.1, le_of_lt h.2⟩
    simp only [if_neg hout]
    linarith
