-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb28_original_finitecap_predictable_quadratic_grid_L2_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:15:52.269355+00:00
-- url     : https://prove2.me/submissions/0a6d876b-89d0-4142-b9bc-9f34035ec22d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb39_orthogonal_sum_second_moment_bound
import Theorems.Thm_AvramDividend_Classical_avram_gb33_original_finitecap_quadratic_grid_cell_orthogonality
import Theorems.Thm_AvramDividend_Classical_avram_gb34_original_finitecap_quadratic_cell_fourth_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- The original-grid quadratic L2 rate follows from individual cell bounds,
    cross-cell orthogonality and the proved finite-sum moment identity. -/
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
      let Q : ℕ → Ω → ℝ := fun m ω =>
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
        (Finset.range (m + 1)).sum (fun i =>
          H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
        Integrable (fun ω => (Q m ω) ^ 2) P ∧
          (∫ ω, (Q m ω) ^ 2 ∂P) ≤ K / ((m + 1 : ℕ) : ℝ) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : ℕ → ℕ → Ω → ℝ := fun m i η =>
    x + X.X (s m i) η - rightLimit D (s m i) η
  let Z : ℕ → ℕ → Ω → ℝ := fun m i η =>
    X.X (s m i + Δ m) η - X.X (s m i) η - (Δ m : ℝ) * X.c
  let G : ℕ → ℕ → Ω → ℝ := fun m i η =>
    if s m i < ρ η then Real.exp (-(q * (s m i : ℝ))) *
      (if Y m i η ∈ Icc a b then deriv w (Y m i η) else 1) else 0
  let H : ℕ → ℕ → Ω → ℝ := fun m i η =>
    if s m i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s m i : ℝ))) *
      (if Y m i η ∈ Icc a b then iteratedDeriv 2 w (Y m i η) else 0) else 0
  let U : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    H m i ω * (Z m i ω ^ 2 - (Δ m : ℝ) * X.σ ^ 2)
  change ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
    Integrable (fun ω => ((Finset.range (m + 1)).sum (fun i => U m i ω)) ^ 2) P ∧
    (∫ ω, ((Finset.range (m + 1)).sum (fun i => U m i ω)) ^ 2 ∂P) ≤
      K / ((m + 1 : ℕ) : ℝ)
  obtain ⟨K, hK, hcell⟩ :=
    avram_gb34_original_finitecap_quadratic_cell_fourth_bound
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA j
  have horth := avram_gb33_original_finitecap_quadratic_grid_cell_orthogonality
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA j
  refine ⟨K, hK, ?_⟩
  intro m
  have hdiag (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      Integrable (fun ω => (U m i ω) ^ 2) P ∧
      (∫ ω, (U m i ω) ^ 2 ∂P) ≤
        K / (((m + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [U, Δ, s, Y, Z, G, H, a, b] using hcell m i hi
  have hoff (i : ℕ) (hi : i ∈ Finset.range (m + 1))
      (r : ℕ) (hr : r ∈ Finset.range (m + 1)) (hir : i ≠ r) :
      Integrable (fun ω => U m i ω * U m r ω) P ∧
      (∫ ω, U m i ω * U m r ω ∂P) = 0 := by
    simpa only [U, Δ, s, Y, Z, G, H, a, b] using horth m i hi r hr hir
  have hsum := avram_gb39_orthogonal_sum_second_moment_bound
    P (Finset.range (m + 1)) (U m) (K / (((m + 1 : ℕ) : ℝ) ^ 2))
    hdiag hoff
  refine ⟨hsum.1, le_trans hsum.2 ?_⟩
  simp only [Finset.card_range]
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  field_simp
  nlinarith
