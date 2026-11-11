-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite62_original_cap_strip_occupation_measurable_ae_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:45:20.667588+00:00
-- url     : https://prove2.me/submissions/ea63e8a7-8f31-4adb-a586-568d203b9863

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite63_unit_occupation_integral_bounds
import Theorems.Thm_AvramDividend_Classical_avram_gfinite64_original_strip_occupation_inner_integrable_ae_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      let b : ℕ → ℝ := fun j =>
        C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Occ : ℕ → Ω → ℝ := fun j ω =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if t < (ρ ω : ℝ) ∧
              b j < riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume
      (∀ j : ℕ, AEStronglyMeasurable
        (A.indicator (Occ j)) P) ∧
      (∀ j : ℕ, ∀ ω : Ω,
        ‖A.indicator (Occ j) ω‖ ≤ (n : ℝ)) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun j : ℕ => A.indicator (Occ j) ω)
          atTop (𝓝 (0 : ℝ))) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let b : ℕ → ℝ := fun j =>
    C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Occ : ℕ → Ω → ℝ := fun j ω =>
    ∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b j < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume
  obtain ⟨hMeas, hInner, hConv⟩ :=
    avram_gfinite64_original_strip_occupation_inner_integrable_ae_vanish
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle
      δ hδ hFloor A hA
  refine ⟨hMeas, ?_, hConv⟩
  intro j ω
  let f : ℝ → ℝ := fun t =>
    if t < (ρ ω : ℝ) ∧
        b j < riskProcess X x D (Real.toNNReal t) ω
    then (1 : ℝ) else 0
  have h0 : ∀ t, 0 ≤ f t := by
    intro t
    dsimp [f]
    split_ifs <;> norm_num
  have h1 : ∀ t, f t ≤ 1 := by
    intro t
    dsimp [f]
    split_ifs <;> norm_num
  obtain ⟨hLow, hUp⟩ :=
    avram_gfinite63_unit_occupation_integral_bounds
      n f (hInner j ω) h0 h1
  have hEq : Occ j ω =
      ∫ t in Ioo (0 : ℝ) (n : ℝ), f t ∂volume := rfl
  have hBound : ‖Occ j ω‖ ≤ (n : ℝ) := by
    rw [hEq, Real.norm_eq_abs, abs_of_nonneg hLow]
    exact hUp
  by_cases hAω : ω ∈ A
  · simpa only [Set.indicator_of_mem hAω] using hBound
  · simp only [Set.indicator_of_notMem hAω, norm_zero]
    exact Nat.cast_nonneg n
