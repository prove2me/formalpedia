-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a538_original_generator_cell_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:32:11.51619+00:00
-- url     : https://prove2.me/submissions/2aa3a2dd-2f64-4671-8357-9d7ee0149417

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a396_original_crossing_compact_C2_generator_coefficients
import Theorems.Thm_AvramDividend_Classical_avram_ga_a540_ae_bounded_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a542_original_generator_cell_aestronglyMeasurable
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
    let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      if 0 < ρ ω ∧ s < ρ ω then
        (Δ : ℝ) * E s * X.generator w (Y s)
      else 0
    ∀ m i : ℕ, i < m →
      Integrable (G m i) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨K, hK, hBound⟩ :=
    avram_ga_a396_original_crossing_compact_C2_generator_coefficients
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ
      hρstop hρle j hprefix
  intro G m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let R : ℝ := (Δ : ℝ) * K
  have hR : 0 ≤ R := by dsimp [R]; exact mul_nonneg (by positivity) hK
  have hMeas :=
    avram_ga_a542_original_generator_cell_aestronglyMeasurable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ
      hρstop hρle j hprefix m i hi
  have hb : ∀ᵐ ω ∂P, |G m i ω| ≤ R := by
    filter_upwards [hBound] with ω hw
    dsimp [G, R]
    by_cases hs : 0 < ρ ω ∧ (i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω
    · simp only [if_pos hs]
      have hcoeff := (hw m i (by simpa only [Δ] using hs.2)).2.2
      have hE0 : 0 ≤ Real.exp (-(q * (((i : ℝ≥0) * Δ) : ℝ))) :=
        (Real.exp_pos _).le
      have hE1 : Real.exp (-(q * (((i : ℝ≥0) * Δ) : ℝ))) ≤ 1 := by
        apply (Real.exp_le_one_iff).2
        exact neg_nonpos.mpr (mul_nonneg hq.le (by positivity))
      change |(Δ : ℝ) * Real.exp (-(q * (((i : ℝ≥0) * Δ) : ℝ))) *
          X.generator w (x + X.X ((i : ℝ≥0) * Δ) ω -
            rightLimit D ((i : ℝ≥0) * Δ) ω)| ≤ (Δ : ℝ) * K
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Δ : ℝ)),
        abs_of_nonneg hE0]
      calc
        (Δ : ℝ) * Real.exp (-(q * (((i : ℝ≥0) * Δ) : ℝ))) *
            |X.generator w (x + X.X ((i : ℝ≥0) * Δ) ω -
              rightLimit D ((i : ℝ≥0) * Δ) ω)| ≤
          (Δ : ℝ) * Real.exp (-(q * (((i : ℝ≥0) * Δ) : ℝ))) * K :=
            mul_le_mul_of_nonneg_left hcoeff (mul_nonneg (by positivity) hE0)
        _ ≤ (Δ : ℝ) * K := by
          calc
            (Δ : ℝ) * Real.exp (-(q * (((i : ℝ≥0) * Δ) : ℝ))) * K =
                (Δ : ℝ) * (Real.exp (-(q * (((i : ℝ≥0) * Δ) : ℝ))) * K) := by ring
            _ ≤ (Δ : ℝ) * K := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_of_le_one_left hK hE1) (by positivity)
    · simp only [if_neg hs, abs_zero]
      exact hR
  exact avram_ga_a540_ae_bounded_real_integrable (G m i) R hR
    hMeas hb (integrable_const R)
