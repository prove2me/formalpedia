-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_full_interior_negative_mark_kernel_any_cofinal_spatial_mask_integral_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:46:24.821297+00:00
-- url     : https://prove2.me/submissions/6ccaa1b4-544f-418e-9f0a-7654c9fc74f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_integrable_original_mark_kernel_eventual_mask_integral_convergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (S : ℝ≥0) (μ : Measure ((ℝ≥0 × Ω) × ℝ)) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    let Interior : Set ((ℝ≥0 × Ω) × ℝ) := {p |
      ((p.1.1 : ℝ≥0∞) ≤
        min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧ p.2 < 0) ∧
      (0 < Y p.1.1 p.1.2 ∧
        ENNReal.ofReal (Y p.1.1 p.1.2) < C)}
    let Full : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p ∈ Interior then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
      else 0
    let Masked : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun n p =>
      if p ∈ Interior ∧ Y p.1.1 p.1.2 ∈ Icc (a n) (b n) then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
      else 0
    let E : ℕ → Set ((ℝ≥0 × Ω) × ℝ) := fun n =>
      {p | p ∉ Interior ∨ Y p.1.1 p.1.2 ∈ Icc (a n) (b n)}
    (∀ n, MeasurableSet (E n)) →
    Integrable Full μ →
    Tendsto (fun n => ∫ p, Masked n p ∂μ)
      atTop (𝓝 (∫ p, Full p ∂μ)) := by
  intro Y Interior Full Masked E hEm hFullI
  have hExhaust : ∀ᵐ p ∂μ, ∀ᶠ n : ℕ in atTop, p ∈ E n := by
    filter_upwards [] with p
    by_cases hInt : p ∈ Interior
    · obtain ⟨N, hN⟩ :=
        hcover (Y p.1.1 p.1.2) hInt.2.1 hInt.2.2
      filter_upwards [eventually_ge_atTop N] with n hn
      exact Or.inr (hN n hn)
    · exact Filter.Eventually.of_forall (fun n => Or.inl hInt)
  have hMask (n : ℕ) :
      (fun p => Masked n p) =
        (fun p => if p ∈ E n then Full p else 0) := by
    funext p
    by_cases hi : p ∈ Interior
    · by_cases hb : Y p.1.1 p.1.2 ∈ Icc (a n) (b n)
      · simp [Masked, Full, E, hi, hb]
      · simp [Masked, Full, E, hi, hb]
    · simp [Masked, Full, E, hi]
  have hDCT :=
    avram_bva_a22_integrable_original_mark_kernel_eventual_mask_integral_convergence
      μ Full hFullI E hEm hExhaust
  have hFun : (fun n : ℕ => ∫ p, Masked n p ∂μ) =
      (fun n : ℕ => ∫ p, if p ∈ E n then Full p else 0 ∂μ) := by
    funext n
    rw [hMask n]
  apply hDCT.congr'
  apply Filter.Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hi : p ∈ Interior
  · by_cases hb : Y p.1.1 p.1.2 ∈ Icc (a n) (b n)
    · simp [Masked, Full, E, hi, hb]
    · simp [Masked, Full, E, hi, hb]
  · simp [Masked, Full, E, hi]
