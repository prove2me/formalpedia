-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a267_original_combined_fullcell_positive_aestrongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:07:36.5742+00:00
-- url     : https://prove2.me/submissions/42a3c3a3-742c-4e79-a0c0-ea1ac0b8aac3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a152_b0_original_fullcell_positive_residual_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a211_zerojump_fullcell_generator_cancel_to_combined_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
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
    let Full : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * R i +
        (iteratedDeriv 2 w (Y (s i)) / 2) * Z i^2)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i else 0
    ∀ m, AEStronglyMeasurable (fun ω => max (Full m ω) 0) P := by
  intro Full m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℕ → Ω → ℝ := fun i ω =>
    x + X.X (s i) ω - rightLimit D (s i) ω
  let R : ℕ → Ω → ℝ := fun i ω =>
    X.X (s i + Δ) ω - X.X (s i) ω
  let Z : ℕ → Ω → ℝ := fun i ω =>
    R i ω - (Δ : ℝ) * X.c
  let H : ℕ → Ω → ℝ := fun i ω =>
    E (s i) * (deriv w (Y i ω) * Z i ω +
      (iteratedDeriv 2 w (Y i ω) / 2) *
        ((Z i ω)^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y i ω)
  let F : ℕ → Ω → ℝ := fun i ω =>
    E (s i + Δ) * (w (Y i ω + R i ω) - w (Y i ω)) -
      H i ω
  let Alt : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i ω else 0
  have hOld := avram_ga_a152_b0_original_fullcell_positive_residual_aestrongly_measurable
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
    ρ hρstop hρle j hprefix m
  have hAlt : AEStronglyMeasurable (fun ω => max (Alt ω) 0) P := by
    simpa only [Alt,F,H,Z,R,Y,E,s,Δ] using hOld
  have hCell (i : ℕ) (ω : Ω) :
      E (s i + Δ) * (w (Y i ω + R i ω) - w (Y i ω)) -
        E (s i) * (deriv w (Y i ω) * R i ω +
          (iteratedDeriv 2 w (Y i ω) / 2) * (Z i ω)^2) =
      F i ω := by
    have hGen := avram_p4_f11_zero_jump_generator_eq_gaussian_drift
      X hNuZero w (Y i ω)
    dsimp [F,H]
    rw [hGen]
    exact (avram_ga_a211_zerojump_fullcell_generator_cancel_to_combined_source
      (E (s i)) (E (s i+Δ)) (w (Y i ω))
      (w (Y i ω+R i ω)) (deriv w (Y i ω))
      (iteratedDeriv 2 w (Y i ω))
      (R i ω) X.c X.σ (Δ : ℝ)).symm
  have hEq (ω : Ω) : Full m ω = Alt ω := by
    change (∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then
        E (s i+Δ)*(w (Y i ω+R i ω)-w (Y i ω)) -
          E (s i)*(deriv w (Y i ω)*R i ω +
            iteratedDeriv 2 w (Y i ω)/2*(Z i ω)^2)
      else 0) = Alt ω
    dsimp only [Alt]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hmask : s i < ρ ω ∧ s i+Δ ≤ ρ ω
    · simp only [if_pos hmask]
      exact hCell i ω
    · simp only [if_neg hmask]
  have hFun : (fun ω => max (Full m ω) 0) =
      (fun ω => max (Alt ω) 0) := by
    funext ω
    rw [hEq ω]
  simpa only [hFun] using hAlt
