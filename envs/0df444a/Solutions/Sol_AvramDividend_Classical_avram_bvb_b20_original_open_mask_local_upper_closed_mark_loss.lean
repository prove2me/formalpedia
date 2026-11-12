-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_original_open_mask_local_upper_closed_mark_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:17:35.552481+00:00
-- url     : https://prove2.me/submissions/7487b056-d40a-4e2f-9524-b68f1bf5b671

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Interior original losses have the closed-cap loss as a local upper envelope. -/
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
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) (q : ℝ)
    (hRateNonpos : ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C →
      (∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) ≤ 0)
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
  dsimp only
  intro hcap
  let U : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r
  let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
  let H : ℝ≥0 → ℝ := fun r =>
    -(Real.exp (-(q * (r : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν)
  have hcont : ContinuousWithinAt H (Ioc 0 t ∩ U ⁻¹' A) t := by
    exact (avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
      X x C D hD ω S t ht htpos hsource hFinite w hw_cont hw_neg
      hw_meas hActivity hνatom q hcap).neg
  have hevent : ∀ᶠ r in 𝓝[Ioc 0 t ∩ U ⁻¹' A] t, H r < H t + ε :=
    hcont.eventually (Iio_mem_nhds (by linarith : H t < H t + ε))
  filter_upwards [hevent] with r hr
  change (if 0 < U r ∧ ENNReal.ofReal (U r) < C then H r else 0) ≤ H t + ε
  split_ifs
  · exact le_of_lt hr
  · have hneg := hRateNonpos (U t) hcap.1 hcap.2
    have hexp := Real.exp_pos (-(q * (t : ℝ)))
    have hprod : Real.exp (-(q * (t : ℝ))) *
        (∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hexp) hneg
    dsimp [H]
    linarith
