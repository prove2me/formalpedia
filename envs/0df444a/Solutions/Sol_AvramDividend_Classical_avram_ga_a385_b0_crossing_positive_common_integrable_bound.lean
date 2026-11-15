-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a385_b0_crossing_positive_common_integrable_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:23:16.008735+00:00
-- url     : https://prove2.me/submissions/05a4c0b7-f7f7-4618-8976-f4fee03705ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a387_b0_crossing_spatial_positive_integrable_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a388_b0_crossing_compensator_absolute_integrable_majorant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

private theorem norm_pospart_sub_le (u v : ℝ) :
    ‖max (u - v) 0‖ ≤ ‖max u 0‖ + ‖v‖ := by
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right (u - v) 0)]
  rw [abs_of_nonneg (le_max_right u 0)]
  apply max_le
  · nlinarith [le_max_left u 0, neg_le_abs v]
  · nlinarith [le_max_right u 0, abs_nonneg v]

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
    let Cross : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let Ccell : ℕ → ℝ := fun i =>
      E (ρ ω) * (w (Y (s i) +
        (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ ρ ω < s i + Δ then Ccell i else 0
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ m, ∀ᵐ ω ∂P, ‖max (Cross m ω) 0‖ ≤ B ω := by
  classical
  intro Cross
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
  let Comp : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if CrossMask m i ω then
        let z := X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
        E (s m i) * (deriv w (Y ω (s m i)) * z +
          (iteratedDeriv 2 w (Y ω (s m i)) / 2) *
            (z^2 - (Δ m : ℝ) * X.σ^2)) +
          (Δ m : ℝ) * E (s m i) * X.generator w (Y ω (s m i))
      else 0

  obtain ⟨B1, hBI1, hDom1⟩ :=
    avram_ga_a387_b0_crossing_spatial_positive_integrable_majorant
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  obtain ⟨B2, hBI2, hDom2⟩ :=
    avram_ga_a388_b0_crossing_compensator_absolute_integrable_majorant
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  refine ⟨(fun ω => B1 ω + B2 ω), hBI1.add hBI2, ?_⟩
  intro m
  filter_upwards [hDom1 m, hDom2 m] with ω hb1 hb2
  have hSplit : Cross m ω = Spatial m ω - Comp m ω := by
    dsimp [Cross, Spatial, Comp, CrossMask, Δ, s, E, Y]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hc : (i : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω ∧
        ρ ω < (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
          (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    · simp [hc] <;> ring
    · simp [hc]
  rw [hSplit]
  exact (norm_pospart_sub_le (Spatial m ω) (Comp m ω)).trans
    (add_le_add hb1 hb2)
