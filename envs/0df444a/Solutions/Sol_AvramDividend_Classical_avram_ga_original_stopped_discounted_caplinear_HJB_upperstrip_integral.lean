-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_stopped_discounted_caplinear_HJB_upperstrip_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:00:47.095488+00:00
-- url     : https://prove2.me/submissions/690fe812-4c7f-47b4-9b81-6c16f2d02113

import Theorems.Thm_AvramDividend_Classical_avram_ga_integrated_discounted_upperstrip_generator_budget
import Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_original_stopped_discounted_caplinear_HJB_upperstrip_ae
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (b : ℝ)
    (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let μ : Measure ℝ := volume.restrict S
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => Real.exp (-(q * t)) *
        (X.generator V (Y t) - q * V (Y t))) μ →
      Integrable (fun t => if b < Y t then (1 : ℝ) else 0) μ →
      (∫ t in S, Real.exp (-(q * t)) *
        (X.generator V (Y t) - q * V (Y t)) ∂volume) ≤
        max X.c 0 * (∫ t in S,
          if b < Y t then (1 : ℝ) else 0 ∂volume) := by
  have hSource :=
    avram_gbB54cp_original_stopped_discounted_caplinear_HJB_upperstrip_ae
      X hBV hν q hq w b hwb hHJB x D hD n ρ δ hδ hFloor
  filter_upwards [hSource] with ω hω
  intro S μ Y V hGI hOccI
  have ht : ∀ᵐ t ∂μ,
      Real.exp (-(q * t)) * (X.generator V (Y t) - q * V (Y t)) ≤
        if b < Y t then max X.c 0 else 0 := by
    simpa only [S, μ, Y, V] using hω
  simpa only [μ] using
    (avram_ga_integrated_discounted_upperstrip_generator_budget
      S q b X.c Y (fun t => X.generator V (Y t) - q * V (Y t))
      hGI hOccI ht)
