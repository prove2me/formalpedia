-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_original_mark_rate_left_continuous_on_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:27:43.962362+00:00
-- url     : https://prove2.me/submissions/8e0b5994-1da7-43ac-b9c5-cfd055ba578e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r
    let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ContinuousWithinAt
      (fun r : ℝ≥0 => ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν)
      (Ioc 0 t ∩ U ⁻¹' A) t := by
  dsimp only
  intro hcap
  let U : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r
  let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
  have hU : ContinuousWithinAt U (Ioc 0 t) t :=
    avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
      X x C D hD ω S t ht htpos hsource
  have hrate : ContinuousWithinAt
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) A (U t) :=
    avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
      C hFinite w hw_cont hw_neg hw_meas X.ν hActivity hνatom
      (U t) hcap.1 hcap.2
  exact hrate.comp_inter hU
