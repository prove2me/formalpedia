-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB57_original_finitecap_linear_grid_cell_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:04:34.461353+00:00
-- url     : https://prove2.me/submissions/f150479b-8014-466b-87b1-c05fc6a2f9ac

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB56_bounded_linear_cell_memLp_two
import Theorems.Thm_AvramDividend_Classical_avram_gbB58_original_finitecap_predictable_G_measurable_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

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
    ∀ (j : ℕ),
      let V : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        G i ω * Z i ω
      ∀ m : ℕ, ∀ i ∈ Finset.range (m + 1),
        MemLp (V m i) 2 P := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j V m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : Ω → ℝ := fun η => x + X.X s η - rightLimit D s η
  let G : Ω → ℝ := fun η =>
    if s < ρ η then Real.exp (-(q * (s : ℝ))) *
      (if Y η ∈ Icc a b then deriv w (Y η) else 1)
    else 0
  let Z : Ω → ℝ := fun η =>
    X.X (s + Δ) η - X.X s η - (Δ : ℝ) * X.c
  change MemLp (fun η => G η * Z η) 2 P
  obtain ⟨B, hB, hGc⟩ :=
    avram_gbB58_original_finitecap_predictable_G_measurable_uniform_bound
      X hX q hq w C hC hFiniteCap hw_smooth x D hD
      n hn ρ hρstop δ hδ j
  have hGm : Measurable G := by
    simpa only [G, Y, s, Δ, a, b] using (hGc m i).1
  have hGb : ∀ η, |G η| ≤ B := by
    intro η
    simpa only [G, Y, s, Δ, a, b] using (hGc m i).2 η
  have hX1 : Measurable (X.X (s + Δ)) :=
    (X.adapted (s + Δ)).mono (𝓕.le _) le_rfl
  have hX0 : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hZm : Measurable Z :=
    (hX1.sub hX0).sub measurable_const
  have hsle : s ≤ s + Δ := by
    exact le_add_of_nonneg_right (by positivity)
  have hZ2 : Integrable (fun η => Z η ^ 2) P := by
    simpa [Z] using
      (avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
        X hν s (s + Δ) hsle).1
  exact avram_gbB56_bounded_linear_cell_memLp_two
    P G Z B hGm hZm hB hGb hZ2
