-- Prove2me | solution 2 for AvramDividend.Classical.avram_gfinite43_original_compact_cash_terminal_diagonal_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:17:30.977913+00:00
-- url     : https://prove2.me/submissions/3b6a4b0d-13dc-42c1-9829-5d31adcb35c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gfinite49_original_positive_clock_cash_mesh_error
import Theorems.Thm_AvramDividend_Classical_avram_gfinite48_original_zero_clock_cash_noise_cancel
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∃ (N : ℕ → ℕ) (E : ℕ → Ω → ℝ),
        let Δ : ℕ → ℝ≥0 := fun j => (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
        let a : ℝ := δ / 2
        let b : ℕ → ℝ := fun j => C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → ℕ → Ω → ℝ := fun j i ω => x + X.X (s j i) ω - rightLimit D (s j i) ω
        let Z : ℕ → ℕ → Ω → ℝ := fun j i ω => X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
        let G : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω) else 1) else 0
        let H : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j) then iteratedDeriv 2 w (Y j i ω) else 0) else 0
        let M : ℕ → Ω → ℝ := fun j ω => (Finset.range (N j + 1)).sum
          (fun i => G j i ω * Z j i ω + H j i ω * (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
        let F : Ω → ℝ := fun ω => if ρ ω = 0 then w x else
          Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
        StrictMono N ∧
        (∀ j, IntegrableOn (E j) A P) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A), 0 ≤ E j ω) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A), F ω ≤ w x + M j ω + E j ω) ∧
        Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA
  obtain ⟨N, hN, E, hEi, hmean, hpath, hzero⟩ :=
    avram_gfinite49_original_positive_clock_cash_mesh_error
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA
  let Δ : ℕ → ℝ≥0 := fun j => (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
  let a : ℝ := δ / 2
  let b : ℕ → ℝ := fun j => C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : ℕ → ℕ → Ω → ℝ := fun j i ω => x + X.X (s j i) ω - rightLimit D (s j i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun j i ω => X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
  let G : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then
    Real.exp (-(q * (s j i : ℝ))) *
      (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω) else 1) else 0
  let H : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then
    (1 / 2 : ℝ) * Real.exp (-(q * (s j i : ℝ))) *
      (if Y j i ω ∈ Icc a (b j) then iteratedDeriv 2 w (Y j i ω) else 0) else 0
  let M : ℕ → Ω → ℝ := fun j ω =>
    (Finset.range (N j + 1)).sum (fun i =>
      G j i ω * Z j i ω + H j i ω *
        (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
  let F : Ω → ℝ := fun ω => if ρ ω = 0 then w x else
    Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
    (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
  let E' : ℕ → Ω → ℝ := fun j ω => max (E j ω) 0
  have hEi' (j : ℕ) : IntegrableOn (E' j) A P := by
    have hI : IntegrableOn (fun ω => (E j ω + |E j ω|) / 2) A P :=
      ((hEi j).add (hEi j).abs).div_const 2
    convert hI using 1
    funext ω
    change max (E j ω) 0 = (E j ω + |E j ω|) / 2
    rcases le_total 0 (E j ω) with hω | hω
    · rw [max_eq_left hω, abs_of_nonneg hω]; ring
    · rw [max_eq_right hω, abs_of_nonpos hω]; ring
  have hnonneg' (j : ℕ) :
      ∀ᵐ ω ∂(P.restrict A), 0 ≤ E' j ω :=
    Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  have hzeroNoise : ∀ j ω, ρ ω = 0 →
      F ω = w x ∧ M j ω = 0 ∧
        max (F ω - w x - M j ω) 0 = 0 := by
    exact avram_gfinite48_original_zero_clock_cash_noise_cancel
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA N
  have hpath' (j : ℕ) :
      ∀ᵐ ω ∂(P.restrict A), F ω ≤ w x + M j ω + E' j ω := by
    filter_upwards [hpath j] with ω hw
    by_cases hρ : ρ ω = 0
    · obtain ⟨hf, hm, _⟩ := hzeroNoise j ω hρ
      rw [hf, hm]
      have hE0 : 0 ≤ E' j ω := le_max_right _ _
      linarith
    · have hP : F ω ≤ w x + M j ω + E j ω := hw hρ
      have hM : E j ω ≤ E' j ω := le_max_left _ _
      linarith
  have hmean' :
      Tendsto (fun j => ∫ ω in A, E' j ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    simpa only [E'] using hmean
  refine ⟨N, E', ?_⟩
  dsimp only
  exact ⟨hN, hEi', hnonneg', hpath', hmean'⟩
