-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a226_original_raw_gaussian_exponential_tail_expected_L1_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:22:26.485477+00:00
-- url     : https://prove2.me/submissions/cc8a3b9d-c2c0-45ee-8511-81715a49b4ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a224_original_true_physical_gaussian_positive_exponential_tail_expected_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a225_original_raw_positive_gaussian_exp_tail_fullmesh_eventual_centered_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n) (θ δ : ℝ)
    (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (R m i ω - (Δ m : ℝ) * X.c) / X.σ
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) P) →
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if δ / (2 * X.σ) ≤ Z m i ω
        then Real.exp ((θ * X.σ) * Z m i ω) else 0) P) →
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  intro Δ s R Z hRI hZI
  let Raw : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0
  let Center : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if δ / (2 * X.σ) ≤ Z m i ω
      then Real.exp ((θ * X.σ) * Z m i ω) else 0
  have hCenter : Tendsto (fun m => ∫ ω, Center m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    have hθ' : 0 ≤ θ * X.σ := mul_nonneg hθ hσ.le
    have hδ' : 0 < δ / (2 * X.σ) := by positivity
    have hG := avram_ga_a224_original_true_physical_gaussian_positive_exponential_tail_expected_L1
      X hν hσ n hn (θ * X.σ) (δ / (2 * X.σ)) hθ' hδ'
    simpa only [Center,Z,R,s,Δ,add_tsub_cancel_left] using hG
  have hUpper : ∀ᶠ m : ℕ in atTop,
      (∫ ω, Raw m ω ∂P) ≤
        Real.exp (θ * δ / 2) * (∫ ω, Center m ω ∂P) := by
    have hPoint := avram_ga_a225_original_raw_positive_gaussian_exp_tail_fullmesh_eventual_centered_bound
      X hσ n θ δ hθ hδ
    change ∀ᶠ m : ℕ in atTop, ∀ ω : Ω,
      Raw m ω ≤ Real.exp (θ * δ / 2) * Center m ω at hPoint
    filter_upwards [hPoint] with m hm
    rw [← integral_const_mul]
    exact integral_mono (hRI m) ((hZI m).const_mul _) (hm)
  have hNonneg (m : ℕ) : 0 ≤ (∫ ω, Raw m ω ∂P) := by
    apply integral_nonneg
    intro ω
    dsimp [Raw]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hTarget : Tendsto (fun m =>
      Real.exp (θ * δ / 2) * (∫ ω, Center m ω ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_const_nhds.mul hCenter using 1 <;> simp
  exact squeeze_zero' (Filter.Eventually.of_forall hNonneg) hUpper hTarget
