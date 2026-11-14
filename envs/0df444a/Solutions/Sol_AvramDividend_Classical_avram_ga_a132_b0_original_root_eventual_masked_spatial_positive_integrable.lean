-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a132_b0_original_root_eventual_masked_spatial_positive_integrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:07:21.635639+00:00
-- url     : https://prove2.me/submissions/58ff0a56-b631-4622-afe6-a1f944ab44c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a131_b0_original_clipped_spatial_m_vs_succ_last_source_identity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a144_original_b0_lastcell_negative_part_integrability_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ga_a145_b0_original_last_negative_clipped_value_integrable_eventually
import Theorems.Thm_AvramDividend_Classical_avram_ga_a146_b0_original_spatial_masked_positive_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_original_spatial_positive_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original Gaussian root eventually integrable source compensated positive spatial residual follows from its proved m+1-cell positive integrability, exact last-cell correction, and source-specific last-cell negative-integrability and measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ) (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let U : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω); let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (∑ i ∈ Finset.range m, E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
      (∑ i ∈ Finset.range m, let s : ℝ≥0 := (i : ℝ≥0) * Δ; if s < ρ ω then let y := Y s; let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c; E s * (deriv w y * z + (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2)) else 0) -
      (∑ i ∈ Finset.range m, let s : ℝ≥0 := (i : ℝ≥0) * Δ; if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω =>
        if 0 < ρ ω then max (U m ω) (0 : ℝ) else 0) P := by
  let R : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω); let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (∑ i ∈ Finset.range m, E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
    (∑ i ∈ Finset.range m, let ss : ℝ≥0 := (i : ℝ≥0) * Δ; if ss < ρ ω then let y := Y ss; let zz := X.X (ss + Δ) ω - X.X ss ω - (Δ : ℝ) * X.c; E ss * (deriv w y * zz + (iteratedDeriv 2 w y / 2) * (zz ^ 2 - (Δ : ℝ) * X.σ ^ 2)) else 0) -
    (∑ i ∈ Finset.range m, let ss : ℝ≥0 := (i : ℝ≥0) * Δ; if ss < ρ ω then (Δ : ℝ) * E ss * X.generator w (Y ss) else 0)
  let S : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω); let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (∑ i ∈ Finset.range (m + 1), E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
    (∑ i ∈ Finset.range m, let ss : ℝ≥0 := (i : ℝ≥0) * Δ; if ss < ρ ω then let y := Y ss; let zz := X.X (ss + Δ) ω - X.X ss ω - (Δ : ℝ) * X.c; E ss * (deriv w y * zz + (iteratedDeriv 2 w y / 2) * (zz ^ 2 - (Δ : ℝ) * X.σ ^ 2)) else 0) -
    (∑ i ∈ Finset.range m, let ss : ℝ≥0 := (i : ℝ≥0) * Δ; if ss < ρ ω then (Δ : ℝ) * E ss * X.generator w (Y ss) else 0)
  let Last : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω); let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      E (v (m + 1)) * (w (Z m) - w (Y (v m)))
  let Um : ℕ → Ω → ℝ := fun m ω => if 0 < ρ ω then R m ω else 0
  let Sm : ℕ → Ω → ℝ := fun m ω => if 0 < ρ ω then S m ω else 0
  let Lm : ℕ → Ω → ℝ := fun m ω => if 0 < ρ ω then Last m ω else 0
  have hDiff (m : ℕ) (ω : Ω) : Um m ω = Sm m ω - Lm m ω := by
    by_cases hp : 0 < ρ ω
    · simp only [Um, Sm, Lm, if_pos hp]
      dsimp only [R, S, Last]
      simp only [Finset.sum_range_succ]
      ring
    · simp only [Um, Sm, Lm, if_neg hp, sub_zero]
  have hSI : ∀ m, Integrable (fun ω => max (Sm m ω) 0) P := by
    intro m
    have h := avram_ga_a26_original_spatial_positive_integrable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m
    convert h using 1
    funext ω
    by_cases hp : 0 < ρ ω
    · simp only [Sm, if_pos hp]
      rfl
    · simp only [Sm, if_neg hp, max_self]
  have hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (Um m ω) 0) P := by
    intro m
    have h := avram_ga_a146_b0_original_spatial_masked_positive_aestrongly_measurable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m
    convert h using 1
    funext ω
    by_cases hp : 0 < ρ ω
    · simp only [Um, if_pos hp]
      rfl
    · simp only [Um, if_neg hp, max_self]
  have hLast : ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (-Lm m ω) 0) P := by
    obtain ⟨k, hk⟩ := avram_ga_a145_b0_original_last_negative_clipped_value_integrable_eventually
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
    refine ⟨k, ?_⟩
    intro m hm
    convert hk m hm using 1
    funext ω
    by_cases hp : 0 < ρ ω
    · simp only [Lm, if_pos hp]
      rfl
    · simp only [Lm, if_neg hp, neg_zero, max_self]
  obtain ⟨k, hk⟩ := avram_ga_a144_original_b0_lastcell_negative_part_integrability_transfer
    P Um Sm Lm hDiff hMeas hSI hLast
  refine ⟨k, ?_⟩
  intro m hm
  have h := hk m hm
  convert h using 1
  funext ω
  by_cases hp : 0 < ρ ω
  · simp only [Um, if_pos hp]
    rfl
  · simp only [Um, if_neg hp, max_self]
