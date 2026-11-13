-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a41_original_terminal_cell_envelope_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:51:15.674212+00:00
-- url     : https://prove2.me/submissions/e23eb24a-98c9-4796-b4de-bc56c6202c35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a41a_original_terminal_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a41b_original_terminal_cell_exponential_bound
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
    ∃ theta K L : ℝ,
      0 ≤ theta ∧ 0 ≤ K ∧ 0 ≤ L ∧
      (∀ m : ℕ, AEStronglyMeasurable (F m) P) ∧
      (∀ m : ℕ, ∀ᵐ ω ∂P,
        ‖F m ω‖ ≤ K * Real.exp (theta * runningSup X (n : ℝ≥0) ω) + L) := by
  obtain ⟨theta,K,L,htheta,hK,hL,hBound⟩ :=
    avram_ga_a41b_original_terminal_cell_exponential_bound X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  exact ⟨theta,K,L,htheta,hK,hL,
    avram_ga_a41a_original_terminal_cell_measurable X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix,
    hBound⟩
