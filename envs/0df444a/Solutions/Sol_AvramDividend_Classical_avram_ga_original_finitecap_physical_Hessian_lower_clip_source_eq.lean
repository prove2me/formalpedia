-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_physical_Hessian_lower_clip_source_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:38:13.232809+00:00
-- url     : https://prove2.me/submissions/de3d4475-aa72-4596-b30b-5d994aecd1bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_active_postpayment_lower_clip_equals_source_Hessian
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ (ω : Ω) (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (q b : ℝ) (w : ℝ → ℝ) (n : ℕ) :
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (s i) ω - rightLimit D (s i) ω
      ∀ i ω,
        (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
          (if Y i ω ∈ Icc (δ / 2) b then iteratedDeriv 2 w (Y i ω) else 0)
        else 0) =
        (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
          (if Y i ω ≤ b then iteratedDeriv 2 w (Y i ω) else 0)
        else 0) := by
  intro m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Y : ℕ → Ω → ℝ := fun i ω =>
    x + X.X (s i) ω - rightLimit D (s i) ω
  have hPost : ∀ i ω, s i < ρ ω → δ ≤ Y i ω := by
    intro i ω hi
    exact avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω (ρ ω) δ (hFloor ω) (s i) hi
  exact avram_ga_original_active_postpayment_lower_clip_equals_source_Hessian
    δ b q hδ w Y s ρ hPost
