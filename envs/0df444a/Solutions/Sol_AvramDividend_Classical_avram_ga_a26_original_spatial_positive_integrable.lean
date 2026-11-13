-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_original_spatial_positive_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:02:42.070576+00:00
-- url     : https://prove2.me/submissions/c3c00194-2851-4cb6-aaa1-e2a9950c7bda

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger24_original_postpayment_raw_compact_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_gledger53_original_clipped_physical_source_positive_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger153_original_gaussian_postpayment_HJB_grid_drift_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gledger144_original_clipped_gaussian_physical_positive_integrable__v3
import Theorems.Thm_AvramDividend_Classical_avram_gledger142_original_physical_gaussian_source_exact_two_error_split__v2
import Theorems.Thm_AvramDividend_Classical_avram_gledger152_measurable_positive_residual_integrable_of_positive_source_and_drift
import Theorems.Thm_AvramDividend_Classical_avram_gledger160_original_clipped_discount_euler_grid_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger161_original_clipped_discount_euler_pathwise_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Transfer original physical positive integrability to the spatial source via the discount Euler rate. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ) (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω); let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (∑ i ∈ Finset.range (m + 1),
        E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := Y s
          let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          E s * (deriv w y * z +
            (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
    ∀ m : ℕ, Integrable (fun ω => if 0 < ρ ω then max (B m ω) (0 : ℝ) else 0) P := by
  intro B m; haveI : IsProbabilityMeasure P := X.isProbability
  let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω); let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i))))
  let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω; let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          Real.exp (-(q * (s : ℝ))) *
            (deriv w y * z + (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0)
  let G : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) * (X.generator w y - q * w y)
        else 0)
  let A : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω); let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      (∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * w (Y (v i))) +
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0

  have hM : Integrable (M m) P :=
    (avram_gledger24_original_postpayment_raw_compact_grid_centered
      X hBV hNuZero q (le_of_lt hq) w C hTopCap hw_smooth
      x hx D hD.1.1 ρ hρstop j n m hprefix).1
  have hS : AEStronglyMeasurable (S m) P :=
    (avram_gledger53_original_clipped_physical_source_positive_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m).1
  have hG : Integrable (G m) P :=
    avram_gledger153_original_gaussian_postpayment_HJB_grid_drift_integrable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m
  have hPhys : Integrable
      (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P :=
    avram_gledger144_original_clipped_gaussian_physical_positive_integrable__v3
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m
  have hAm : AEStronglyMeasurable (A m) P :=
    avram_gledger160_original_clipped_discount_euler_grid_aestronglyMeasurable
      X hX q hq w C hC hTopCap hw_smooth x hx hxc D hD n hn τ hτeq ρ hρstop hρle j hprefix m
  obtain ⟨K, hK, hRate⟩ :=
    avram_gledger161_original_clipped_discount_euler_pathwise_rate
      X hX q hq w C hC hTopCap hw_smooth x hx hxc D hD n hn τ hτeq ρ hρstop hρle j hprefix
  have hANorm : ∀ᵐ ω ∂P, ‖A m ω‖ ≤ K / ((m : ℝ) + 1) := by
    filter_upwards [hRate m] with ω hω
    simpa only [Real.norm_eq_abs] using hω
  have hA : Integrable (A m) P :=
    (integrable_const (K / ((m : ℝ) + 1))).mono' hAm hANorm
  have hSMeas : AEStronglyMeasurable
      (fun ω => S m ω - M m ω - G m ω) P :=
    (hS.sub hM.aestronglyMeasurable).sub hG.aestronglyMeasurable
  have hsplit (ω : Ω) : S m ω - M m ω - G m ω = A m ω + B m ω := by
    exact avram_gledger142_original_physical_gaussian_source_exact_two_error_split__v2
      X q w x D n ρ m ω
  have hResidual : Integrable (fun ω =>
      max ((S m ω - M m ω - G m ω) - A m ω) (0 : ℝ)) P :=
    avram_gledger152_measurable_positive_residual_integrable_of_positive_source_and_drift
      P (fun ω => S m ω - M m ω - G m ω) (A m) hPhys hSMeas hA
  have hBm : Integrable (fun ω => max (B m ω) (0 : ℝ)) P := by
    convert hResidual using 1
    ext ω; congr 1
    rw [hsplit ω]; ring
  have hzero (ω : Ω) (h0 : ¬ 0 < ρ ω) : B m ω = 0 := by
    have hr : ρ ω = 0 := le_antisymm (le_of_not_gt h0) (zero_le)
    simp [B, hr]
  have heq : (fun ω => if 0 < ρ ω then max (B m ω) (0 : ℝ) else 0) =
      (fun ω => max (B m ω) (0 : ℝ)) := by
    funext ω; by_cases hpos : 0 < ρ ω
    · simp [hpos]
    · simp [hpos, hzero ω hpos]
  rw [heq]; exact hBm
