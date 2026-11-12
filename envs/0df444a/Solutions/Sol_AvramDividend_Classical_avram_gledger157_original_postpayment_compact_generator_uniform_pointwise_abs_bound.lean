-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger157_original_postpayment_compact_generator_uniform_pointwise_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:37:11.570258+00:00
-- url     : https://prove2.me/submissions/822a1960-ac9b-4976-bd19-40039858cf67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
import Theorems.Thm_AvramDividend_Classical_avram_gledger156_original_zerojump_gaussian_generator_compact_C2_abs_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation)
    (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      |X.generator w (x + X.X t ω - rightLimit D t ω) -
        q * w (x + X.X t ω - rightLimit D t ω)| ≤ B := by
  let a : ℝ := 1 / ((j : ℝ) + 1)
  let b : ℝ := x + ((j : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    have hsmall : 1 / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    dsimp [a, b]
    linarith
  have hbcap : ENNReal.ofReal b < C := by simp [hTopCap]
  obtain ⟨M, hM, hJet⟩ :=
    avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
      X x D hD.1.1 C w hw_smooth a b ha hab hbcap
  let B : ℝ := (X.σ ^ 2 / 2 + |X.c| + q) * M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [
    avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
      X x D hD.1.1 ρ j hprefix] with ω hBand
  intro t ht
  have hy : x + X.X t ω - rightLimit D t ω ∈ Set.Icc a b := by
    have h := hBand t ht
    exact ⟨h.1, h.2⟩
  obtain ⟨hw, hd, hdd⟩ := hJet ω t hy
  have hHess :
      |iteratedDeriv 2 w (x + X.X t ω - rightLimit D t ω)| ≤ M := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hdd
  exact avram_gledger156_original_zerojump_gaussian_generator_compact_C2_abs_bound
    X hNuZero q (le_of_lt hq) w
    (x + X.X t ω - rightLimit D t ω) M hM hw hd hHess

