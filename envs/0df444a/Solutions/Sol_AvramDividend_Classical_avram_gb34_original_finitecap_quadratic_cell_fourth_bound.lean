-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb34_original_finitecap_quadratic_cell_fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:51:17.76303+00:00
-- url     : https://prove2.me/submissions/9c81a989-09c4-42cd-9ec3-494f4cf5f546

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb41_original_gaussian_quadratic_cell_fourth_moment
import Theorems.Thm_AvramDividend_Classical_avram_gb44_original_finitecap_predictable_H_measurable_uniform_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- The original Hessian and intrinsic Gaussian moment atoms imply gb34. -/
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
      let U : ℕ → ℕ → Ω → ℝ := fun m i ω =>
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
        H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2)
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ∈ Finset.range (m + 1),
        Integrable (fun ω => (U m i ω) ^ 2) P ∧
          (∫ ω, (U m i ω) ^ 2 ∂P) ≤
            K / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let Y : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    x + X.X (s m i) ω - rightLimit D (s m i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
  let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if s m i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s m i : ℝ))) *
      (if Y m i ω ∈ Icc (δ / 2) (C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))) then
        iteratedDeriv 2 w (Y m i ω) else 0) else 0
  let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    Z m i ω ^ 2 - (Δ m : ℝ) * X.σ ^ 2
  let U : ℕ → ℕ → Ω → ℝ := fun m i ω => H m i ω * R m i ω
  change ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ∈ Finset.range (m + 1),
    Integrable (fun ω => (U m i ω) ^ 2) P ∧
      (∫ ω, (U m i ω) ^ 2 ∂P) ≤ K / (((m + 1 : ℕ) : ℝ) ^ 2)
  obtain ⟨B, hB, hH⟩ :=
    avram_gb44_original_finitecap_predictable_H_measurable_uniform_bound
      X hX q hq w C hC hFiniteCap hw_smooth x D hD
      n hn ρ hρstop δ hδ j
  obtain ⟨M, hM, hR⟩ :=
    avram_gb41_original_gaussian_quadratic_cell_fourth_moment
      X hX hν n hn
  refine ⟨B ^ 2 * M, mul_nonneg (sq_nonneg _) hM, ?_⟩
  intro m i hi
  have hHi : Measurable (H m i) ∧ ∀ ω, |H m i ω| ≤ B := by
    simpa only [H, Δ, s, Y] using hH m i
  have hRi : Integrable (fun ω => (R m i ω) ^ 2) P ∧
      (∫ ω, (R m i ω) ^ 2 ∂P) ≤
        M / (((m + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [R, Z, Δ, s] using hR m i hi
  have hmajor : Integrable (fun ω => B ^ 2 * (R m i ω) ^ 2) P :=
    hRi.1.const_mul (B ^ 2)
  have hmeas : AEStronglyMeasurable (fun ω => (U m i ω) ^ 2) P := by
    have ht := (hHi.1.pow_const 2).aestronglyMeasurable.mul
      hRi.1.aestronglyMeasurable
    have heq : (fun ω => (U m i ω) ^ 2) =
        (fun ω => (H m i ω) ^ 2 * (R m i ω) ^ 2) := by
      funext ω
      simp only [U, mul_pow]
    rw [heq]
    exact ht
  have hpoint (ω : Ω) : (U m i ω) ^ 2 ≤
      B ^ 2 * (R m i ω) ^ 2 := by
    have hh : (H m i ω) ^ 2 ≤ B ^ 2 := by
      nlinarith [sq_abs (H m i ω), abs_nonneg (H m i ω),
        sq_nonneg (B - |H m i ω|), hHi.2 ω]
    calc
      _ = (H m i ω) ^ 2 * (R m i ω) ^ 2 := by ring
      _ ≤ B ^ 2 * (R m i ω) ^ 2 :=
        mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  have hu : Integrable (fun ω => (U m i ω) ^ 2) P := by
    apply Integrable.mono' hmajor hmeas
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  refine ⟨hu, ?_⟩
  calc
    (∫ ω, (U m i ω) ^ 2 ∂P) ≤
        ∫ ω, B ^ 2 * (R m i ω) ^ 2 ∂P :=
      integral_mono hu hmajor hpoint
    _ = B ^ 2 * (∫ ω, (R m i ω) ^ 2 ∂P) :=
      integral_const_mul _ _
    _ ≤ B ^ 2 * (M / (((m + 1 : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hRi.2 (sq_nonneg _)
    _ = B ^ 2 * M / (((m + 1 : ℕ) : ℝ) ^ 2) := by ring
