-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a396_original_crossing_compact_C2_generator_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:59:58.922009+00:00
-- url     : https://prove2.me/submissions/a3b9ed73-61d9-4283-b1be-609c4a23da89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ (m i : ℕ),
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        s < ρ ω →
          |deriv w (x + X.X s ω - rightLimit D s ω)| ≤ K ∧
          |iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)| ≤ K ∧
          |X.generator w (x + X.X s ω - rightLimit D s ω)| ≤ K := by
  obtain ⟨M,hM,hJet⟩ :=
    avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
      X x hx D hD.1.1 w C hTopCap hw_smooth ρ j hprefix
  let a : ℝ := |X.σ^2 / 2|
  let b : ℝ := |X.c|
  let K : ℝ := M + a * M + b * M
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [hJet] with ω hω
  intro m i Δ s hs
  obtain ⟨hval,hder,hsecond⟩ := hω s hs
  let y : ℝ := x + X.X s ω - rightLimit D s ω
  have hHess : |iteratedDeriv 2 w y| ≤ M := by
    have heq : iteratedDeriv 2 w y = deriv (deriv w) y := by
      simp [iteratedDeriv_succ]
    simpa only [heq] using hsecond
  have hGen : |X.generator w y| ≤ a * M + b * M := by
    rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hNuZero]
    calc
      |X.σ^2 / 2 * iteratedDeriv 2 w y + X.c * deriv w y|
          ≤ |X.σ^2 / 2 * iteratedDeriv 2 w y| +
              |X.c * deriv w y| := abs_add_le _ _
      _ = a * |iteratedDeriv 2 w y| + b * |deriv w y| := by
        rw [abs_mul, abs_mul]
      _ ≤ a * M + b * M := add_le_add
        (mul_le_mul_of_nonneg_left hHess ha)
        (mul_le_mul_of_nonneg_left hder hb)
  refine ⟨?_, ?_, ?_⟩
  · exact hder.trans (by dsimp [K]; nlinarith [mul_nonneg ha hM, mul_nonneg hb hM])
  · exact hHess.trans (by dsimp [K]; nlinarith [mul_nonneg ha hM, mul_nonneg hb hM])
  · exact hGen.trans (by dsimp [K]; linarith)
