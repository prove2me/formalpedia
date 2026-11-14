-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a190_original_stopped_source_small_raw_C2_Taylor_cell_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:59:34.714858+00:00
-- url     : https://prove2.me/submissions/12f803b2-70f5-41bc-b398-c2f582df00d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a76_original_stopped_safe_small_source_classical_Taylor_modulus
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original right-limit dividend-controlled Gaussian source has a uniform
small physical-increment C2 Taylor modulus on the genuine stopped prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hTopCap : C = ⊤) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < ρ ω →
        |X.X t ω - X.X s ω| < δ →
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        let r : ℝ := X.X t ω - X.X s ω
        |w (y + r) - w y - deriv w y * r -
          (iteratedDeriv 2 w y * r^2) / 2| ≤ ε * r^2 := by
  classical
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
  have hCap : ENNReal.ofReal (b + a / 2) < C := by
    simp [hTopCap]
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hDiff : ∀ y ∈ Icc (a / 2) (b + a / 2),
      DifferentiableAt ℝ w y := by
    intro y hy
    have hpos : 0 < y := lt_of_lt_of_le (by positivity : 0 < a / 2) hy.1
    have hmem : y ∈ {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} :=
      ⟨hpos, by simp [hTopCap]⟩
    exact (hw.differentiableOn (by norm_num) y hmem).differentiableAt
      (hopen.mem_nhds hmem)
  have hBand : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < ρ ω →
      x + X.X s ω - rightLimit D s ω ∈ Icc a b := by
    filter_upwards [avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
      X x D hD ρ j hprefix] with ω hω
    intro s hs
    exact hω s hs
  intro ε hε
  obtain ⟨δ,hδ,hMod⟩ :=
    avram_ga_a76_original_stopped_safe_small_source_classical_Taylor_modulus
      X x D hD ρ C w hw a b ha hab hCap hDiff hBand ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hMod] with ω hω
  intro s t hs hsmall
  let r : ℝ := X.X t ω - X.X s ω
  by_cases hr : r = 0
  · simp [r,hr]
  · have hSingleton := hω ({0}) (fun _ => s) (fun _ => t) (by
      intro i hi
      have h0 : i = 0 := Finset.mem_singleton.mp hi
      subst i
      exact ⟨hs,hr,hsmall⟩)
    have hZ : x + X.X t ω - rightLimit D s ω =
        x + X.X s ω - rightLimit D s ω + r := by
      dsimp [r]
      ring
    simpa only [Finset.sum_singleton, hZ] using hSingleton
