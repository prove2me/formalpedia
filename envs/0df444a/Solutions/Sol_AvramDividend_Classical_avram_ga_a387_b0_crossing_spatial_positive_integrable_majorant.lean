-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a387_b0_crossing_spatial_positive_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:45:12.11269+00:00
-- url     : https://prove2.me/submissions/a358dc35-f0eb-4857-8c3c-f2860f322467

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a392_unique_masked_sum_positive_dominated
import Theorems.Thm_AvramDividend_Classical_avram_ga_a393_true_crossing_spatial_one_sided_exp_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a380_monotone_grid_unique_crossing_v2
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
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
    let Spatial : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if CrossMask m i ω then
          E (ρ ω) * (w (Y ω (s m i) +
            (X.X (ρ ω) ω - X.X (s m i) ω)) - w (Y ω (s m i)))
        else 0
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ (m : ℕ), ∀ᵐ ω ∂P, ‖max (Spatial m ω) 0‖ ≤ B ω := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro Δ s E Y CrossMask Spatial
  obtain ⟨θ, K, b, hθ, hK, hb, hCell⟩ :=
    avram_ga_a393_true_crossing_spatial_one_sided_exp_bound
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  let B : Ω → ℝ := fun ω =>
    K * Real.exp (θ * runningSup X (n : ℝ≥0) ω) + b
  have hSigma : 0 < X.σ :=
    lt_of_le_of_ne X.σ_nonneg (Ne.symm hSigmaNonzero)
  have hBI : Integrable B P := by
    have hExp : Integrable (fun ω : Ω =>
        Real.exp (θ * runningSup X (n : ℝ≥0) ω)) P :=
      avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable X hSigma n θ hθ
    exact (hExp.const_mul K).add
      (integrable_const _)
  refine ⟨B, hBI, ?_⟩
  intro m
  filter_upwards [hCell m] with ω hω
  have hΔ : 0 < Δ m := by
    dsimp [Δ]
    have hn' : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
    exact div_pos hn' (by positivity)
  have hsstep (i : ℕ) : s m (i+1) = s m i + Δ m := by
    dsimp [s]
    rw [Nat.cast_succ, add_mul, one_mul]
  have hstrict : StrictMono (s m) := by
    intro i k hik
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hik) hΔ
  have hunique : ∀ i k, CrossMask m i ω → CrossMask m k ω → i = k := by
    intro i k hi hk
    exact avram_ga_a380_monotone_grid_unique_crossing_v2
      (s m) hstrict (ρ ω) i k
      ⟨hi.1, by simpa only [hsstep] using hi.2⟩
      ⟨hk.1, by simpa only [hsstep] using hk.2⟩
  have hB0 : 0 ≤ B ω := by
    dsimp [B]
    exact add_nonneg (mul_nonneg hK (le_of_lt (Real.exp_pos _))) hb
  have hcell (i : ℕ) (hi : i < m) (hci : CrossMask m i ω) :
      max (E (ρ ω) * (w (Y ω (s m i) +
        (X.X (ρ ω) ω - X.X (s m i) ω)) - w (Y ω (s m i)))) 0
        ≤ B ω := by
    have hh := hω i hi hci.1 hci.2
    have heq : Y ω (s m i) + (X.X (ρ ω) ω - X.X (s m i) ω) =
        x + X.X (ρ ω) ω - rightLimit D (s m i) ω := by
      dsimp [Y]
      ring
    rw [heq]
    exact hh
  have hSum := avram_ga_a392_unique_masked_sum_positive_dominated
    m (fun i => CrossMask m i ω)
    (fun i => E (ρ ω) * (w (Y ω (s m i) +
      (X.X (ρ ω) ω - X.X (s m i) ω)) - w (Y ω (s m i))))
    (B ω) hB0 hunique hcell
  have hNonneg : 0 ≤ max (Spatial m ω) 0 := le_max_right _ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hNonneg, Spatial] using hSum
