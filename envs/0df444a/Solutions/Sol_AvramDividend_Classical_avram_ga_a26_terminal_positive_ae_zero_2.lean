-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a26_terminal_positive_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:58:55.609337+00:00
-- url     : https://prove2.me/submissions/eaa12440-7054-453c-90ad-0399f81839fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_terminal_spatial_eventually_zero_pre_horizon
import Theorems.Thm_AvramDividend_Classical_avram_ga_a28_terminal_horizon_ge_ae_zero
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
    let Last : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      E (v (m + 1)) * (w (Z m) - w (Y (v m)))
    let F : ℕ → Ω → ℝ := fun m ω =>
      if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0
    ∀ᵐ ω ∂P, Tendsto (fun m => F m ω) atTop (nhds (0 : ℝ)) := by
  let Last : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    E (v (m + 1)) * (w (Z m) - w (Y (v m)))
  let F : ℕ → Ω → ℝ := fun m ω =>
    if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0
  change ∀ᵐ ω ∂P, Tendsto (fun m => F m ω) atTop (nhds (0 : ℝ))
  have hhorizon :=
    AvramDividend.Classical.avram_ga_a28_terminal_horizon_ge_ae_zero
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
      x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  filter_upwards [hhorizon] with ω hω
  by_cases hlt : ρ ω < (n : ℝ≥0)
  · have hzero :=
      AvramDividend.Classical.avram_ga_a27_terminal_spatial_eventually_zero_pre_horizon
        X.X (rightLimit D) w x (n : ℝ≥0) ρ ω hlt
    have hEventually : ∀ᶠ m : ℕ in atTop, F m ω = (0 : ℝ) := by
      filter_upwards [hzero] with m hzm
      have hlast : Last m ω = 0 := by
        dsimp [Last]
        rw [hzm]
        ring
      by_cases hρ0 : 0 < ρ ω
      · simp [F, hρ0, hlast]
      · simp [F, hρ0]
    have hsym : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] (fun m => F m ω) :=
      hEventually.mono (fun m hm => hm.symm)
    exact Filter.Tendsto.congr' hsym tendsto_const_nhds
  · exact hω (le_of_not_gt hlt)
