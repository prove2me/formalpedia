-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite43_original_compact_cash_terminal_diagonal_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:43:35.260206+00:00
-- url     : https://prove2.me/submissions/430339e0-f3e4-447e-bb66-be958b227715
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite44_original_cash_positive_part_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Reduce the original stopped Gaussian cash ledger to the explicit
    positive-part L1 physical residual along one increasing mesh. -/
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
      ∃ (N : ℕ → ℕ) (E : ℕ → Ω → ℝ),
        let Δ : ℕ → ℝ≥0 := fun j =>
          (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
        let a : ℝ := δ / 2
        let b : ℕ → ℝ := fun j =>
          C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          x + X.X (s j i) ω - rightLimit D (s j i) ω
        let Z : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
        let G : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          if s j i < ρ ω then Real.exp (-(q * (s j i : ℝ))) *
            (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω)
             else 1) else 0
        let H : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          if s j i < ρ ω then (1 / 2 : ℝ) *
            Real.exp (-(q * (s j i : ℝ))) *
            (if Y j i ω ∈ Icc a (b j)
             then iteratedDeriv 2 w (Y j i ω) else 0) else 0
        let M : ℕ → Ω → ℝ := fun j ω =>
          (Finset.range (N j + 1)).sum (fun i =>
            G j i ω * Z j i ω + H j i ω *
              (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
        let F : Ω → ℝ := fun ω =>
          if ρ ω = 0 then w x else
            Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z)))
              ∂(dividendMeasure D ω)).toReal
        StrictMono N ∧
        (∀ j, IntegrableOn (E j) A P) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A), 0 ≤ E j ω) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A),
          F ω ≤ w x + M j ω + E j ω) ∧
        Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let F : Ω → ℝ := fun ω => if ρ ω = 0 then w x else
    Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
    (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
  let M : (ℕ → ℕ) → ℕ → Ω → ℝ := fun N j ω =>
    let Δ : ℕ → ℝ≥0 := fun j => (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
    let a : ℝ := δ / 2
    let b : ℕ → ℝ := fun j =>
      C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℕ → ℕ → Ω → ℝ := fun j i ω =>
      x + X.X (s j i) ω - rightLimit D (s j i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun j i ω =>
      X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
    let G : ℕ → ℕ → Ω → ℝ := fun j i ω =>
      if s j i < ρ ω then Real.exp (-(q * (s j i : ℝ))) *
        (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω) else 1) else 0
    let H : ℕ → ℕ → Ω → ℝ := fun j i ω =>
      if s j i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s j i : ℝ))) *
        (if Y j i ω ∈ Icc a (b j) then iteratedDeriv 2 w (Y j i ω) else 0) else 0
    (Finset.range (N j + 1)).sum (fun i =>
      G j i ω * Z j i ω + H j i ω *
        (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
  /- The sole hard analytic child: the original stopped cash ledger,
     including initial right payment, positive stopped endpoint, and the
     finite-cap boundary, has vanishing positive L1 Gaussian-grid excess. -/
  have hPhysical : ∃ N : ℕ → ℕ, StrictMono N ∧
      (∀ j, IntegrableOn (fun ω => max (F ω - w x - M N j ω) 0) A P) ∧
      Tendsto (fun j => ∫ ω in A, max (F ω - w x - M N j ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [F, M] using
      (avram_gfinite44_original_cash_positive_part_L1
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop σ hσstop hσle
        k ρ hρstop hρle δ hδ hFloor A hA)
  obtain ⟨N, hN, hInt, hSmall⟩ := hPhysical
  let E : ℕ → Ω → ℝ := fun j ω => max (F ω - w x - M N j ω) 0
  refine ⟨N, E, ?_⟩
  change StrictMono N ∧ (∀ j, IntegrableOn (E j) A P) ∧
    (∀ j, ∀ᵐ ω ∂(P.restrict A), 0 ≤ E j ω) ∧
    (∀ j, ∀ᵐ ω ∂(P.restrict A), F ω ≤ w x + M N j ω + E j ω) ∧
    Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ))
  refine ⟨hN, hInt, ?_, ?_, hSmall⟩
  · intro j
    filter_upwards [] with ω
    exact le_max_right _ _
  · intro j
    filter_upwards [] with ω
    have hh : F ω - w x - M N j ω ≤ E j ω := le_max_left _ _
    linarith
