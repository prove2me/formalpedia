-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB51_original_stopped_gaussian_generator_le_true_prepayment_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:13:42.355745+00:00
-- url     : https://prove2.me/submissions/6d69a2d5-8222-48fc-b1c6-6269102c21e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_strict_clock_gaussian_caplinear_occupation_drift_envelope
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω t, 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z =>
        if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => X.generator V (Y t) - q * V (Y t))
        (volume.restrict S) →
      Integrable (fun t => if b < Y t then max X.c 0 else 0)
        (volume.restrict S) →
      Integrable (fun t =>
        if b < riskProcess X x D (Real.toNNReal t) ω
        then max X.c 0 else 0)
        (volume.restrict S) →
      (∫ t, X.generator V (Y t) - q * V (Y t) ∂(volume.restrict S)) ≤
        (∫ t, if b < riskProcess X x D (Real.toNNReal t) ω
          then max X.c 0 else 0 ∂(volume.restrict S)) := by
  have hDrift :=
    avram_gbB41_original_strict_clock_gaussian_caplinear_occupation_drift_envelope
      X hBV hν x b D hD n ρ δ hδ hFloor w q hq hwb hHJB
  filter_upwards [hDrift] with ω hω
  let S : Set ℝ := {t : ℝ |
    0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
  let Y : ℝ → ℝ := fun t =>
    x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
  let V : ℝ → ℝ := fun z =>
    if z ≤ b then w z else w b + (z - b)
  change
    Integrable (fun t => X.generator V (Y t) - q * V (Y t))
      (volume.restrict S) →
    Integrable (fun t => if b < Y t then max X.c 0 else 0)
      (volume.restrict S) →
    Integrable (fun t =>
      if b < riskProcess X x D (Real.toNNReal t) ω
      then max X.c 0 else 0) (volume.restrict S) →
    (∫ t, X.generator V (Y t) - q * V (Y t) ∂(volume.restrict S)) ≤
      (∫ t, if b < riskProcess X x D (Real.toNNReal t) ω
        then max X.c 0 else 0 ∂(volume.restrict S))
  intro hInt hPost hPre
  have hPoint (t : ℝ) :
      (if b < x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω
        then max X.c 0 else 0) ≤
      (if b < riskProcess X x D (Real.toNNReal t) ω
        then max X.c 0 else 0) := by
    have hIndicator :=
      avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
        X x b D hD ω (Real.toNNReal t)
    by_cases hpost : b < x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω
    · by_cases hpre : b < riskProcess X x D (Real.toNNReal t) ω
      · simp [hpost, hpre]
      · have hBad : (1 : ℝ) ≤ 0 := by
          simpa only [if_pos hpost, if_neg hpre] using hIndicator
        norm_num at hBad
    · by_cases hpre : b < riskProcess X x D (Real.toNNReal t) ω
      · simp only [if_neg hpost, if_pos hpre]
        exact le_max_right X.c 0
      · simp [hpost, hpre]
  have hBound := integral_mono_ae hPost hPre
    (Filter.Eventually.of_forall hPoint)
  exact le_trans (hω hInt hPost) hBound
