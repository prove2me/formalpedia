-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:16:46.221766+00:00
-- url     : https://prove2.me/submissions/8bf7bf5c-50e0-4536-b554-b4dbbda33ee4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual right-limit dividend-controlled pre-stop reserve has a uniform
compact C2 envelope for the original source value and its two derivatives. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      let y := x + X.X t ω - rightLimit D t ω
      |w y| ≤ M ∧ |deriv w y| ≤ M ∧ |deriv (deriv w) y| ≤ M := by
  let a : ℝ := 1 / ((j : ℝ) + 1)
  let b : ℝ := x + ((j : ℝ) + 1)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hden : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    have h1 : a ≤ 1 := by
      dsimp [a]
      exact (div_le_iff₀ hden).2 (by nlinarith)
    have h2 : 1 ≤ b := by dsimp [b]; linarith
    exact h1.trans h2
  have hCap : ENNReal.ofReal b < C := by simp [hTopCap]
  obtain ⟨M,hM,hJet⟩ :=
    avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
      X x D hD C w hw a b ha hab hCap
  refine ⟨M,hM,?_⟩
  have hSourceBand :=
    avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
      X x D hD ρ j hprefix
  filter_upwards [hSourceBand] with ω hω
  intro t ht
  exact hJet ω t (hω t ht)
