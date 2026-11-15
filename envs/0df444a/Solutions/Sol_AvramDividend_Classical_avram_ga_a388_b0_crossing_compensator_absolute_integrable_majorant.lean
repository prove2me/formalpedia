-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a388_b0_crossing_compensator_absolute_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:00:50.092296+00:00
-- url     : https://prove2.me/submissions/8fa6897d-73d8-4e84-8ae7-9942bc2ad436

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a394_unique_masked_sum_absolute_dominated
import Theorems.Thm_AvramDividend_Classical_avram_ga_a395_true_crossing_HJB_percell_common_integrable_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a380_monotone_grid_unique_crossing_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

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
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : Ω → ℝ≥0 → ℝ := fun ω t => x + X.X t ω - rightLimit D t ω
    let CrossMask : ℕ → ℕ → Ω → Prop := fun m i ω =>
      s m i < ρ ω ∧ ρ ω < s m i + Δ m
    let Comp : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if CrossMask m i ω then
          let z := X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
          E (s m i) * (deriv w (Y ω (s m i)) * z +
            (iteratedDeriv 2 w (Y ω (s m i)) / 2) *
              (z^2 - (Δ m : ℝ) * X.σ^2)) +
            (Δ m : ℝ) * E (s m i) * X.generator w (Y ω (s m i))
        else 0
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ (m : ℕ), ∀ᵐ ω ∂P, ‖Comp m ω‖ ≤ B ω := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro Δ s E Y CrossMask Comp
  let Hcell : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    let z := X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
    E (s m i) * (deriv w (Y ω (s m i)) * z +
      (iteratedDeriv 2 w (Y ω (s m i)) / 2) *
        (z^2 - (Δ m : ℝ) * X.σ^2)) +
      (Δ m : ℝ) * E (s m i) * X.generator w (Y ω (s m i))
  obtain ⟨B, hBI, hCell⟩ :=
    avram_ga_a395_true_crossing_HJB_percell_common_integrable_majorant
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  let G : Ω → ℝ := fun ω => |B ω|
  have hGI : Integrable G P := Integrable.abs hBI
  refine ⟨G, hGI, ?_⟩
  intro m
  filter_upwards [hCell m] with ω hω
  have hΔ : 0 < Δ m := by
    dsimp [Δ]
    have hn' : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
    exact div_pos hn' (by positivity)
  have hsstep (i : ℕ) : s m (i+1) = s m i + Δ m := by
    dsimp [s]; rw [Nat.cast_succ, add_mul, one_mul]
  have hstrict : StrictMono (s m) := by
    intro i k hik
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hik) hΔ
  have hunique : ∀ i k, CrossMask m i ω → CrossMask m k ω → i = k := by
    intro i k hi hk
    exact avram_ga_a380_monotone_grid_unique_crossing_v2
      (s m) hstrict (ρ ω) i k
      ⟨hi.1, by simpa only [hsstep] using hi.2⟩
      ⟨hk.1, by simpa only [hsstep] using hk.2⟩
  have hcell (i : ℕ) (hi : i < m) (hc : CrossMask m i ω) :
      |Hcell m i ω| ≤ G ω := by
    exact (hω i hi hc.1 hc.2).trans (le_abs_self _)
  have hSum := avram_ga_a394_unique_masked_sum_absolute_dominated
    m (fun i => CrossMask m i ω) (fun i => Hcell m i ω)
    (G ω) (abs_nonneg _) hunique hcell
  have hEq : Comp m ω =
      ∑ i ∈ Finset.range m,
        if CrossMask m i ω then Hcell m i ω else 0 := rfl
  calc
    ‖Comp m ω‖ = |Comp m ω| := Real.norm_eq_abs _
    _ = |∑ i ∈ Finset.range m,
      if CrossMask m i ω then Hcell m i ω else 0| := by rw [hEq]
    _ ≤ G ω := hSum
