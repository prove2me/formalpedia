-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB182_long_tube_original_GH_L1_noise_bound_with_grid_overshoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:12:16.370258+00:00
-- url     : https://prove2.me/submissions/3eaed461-67ed-4767-b23d-30df546fb7e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB159_original_GH_stopped_L1_noise_control_from_centered_Brownian_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
noncomputable section
/-- Long source tube controls original Gaussian whole-grid centered physical increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A)
    (m0 : ℕ) (T : ℝ≥0) (s : ℕ → ℕ → ℝ≥0)
    (Δ : ℕ → ℝ≥0)
    (hs : ∀ m, Monotone (s m))
    (hs0 : ∀ m, s m 0 = 0)
    (hstep : ∀ m i, s m (i + 1) = s m i + Δ m)
    (hX0 : ∀ ω, X.X 0 ω = 0)
    (q ε a : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (w : ℝ → ℝ)
    (B : Ω → ℝ≥0 → ℝ)
    (hT : T ≤ (1 / 1000 : ℝ≥0))
    (hSource : ∀ ω, ω ∈ A → ∀ s : ℝ≥0,
      s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B ω s + 2 * (s : ℝ))
    (hCentered : ∀ ω, ω ∈ A → ∀ s : ℝ≥0,
      s ≤ (1 / 1000 : ℝ≥0) →
      |B ω s| ≤ (1 / 4000 : ℝ))
    (hLongSource : ∀ ω, ω ∈ A → ∀ u : ℝ≥0,
      u ≤ (17 / 16000 : ℝ≥0) →
      X.X u ω = B ω u + 2 * (u : ℝ))
    (hLongCentered : ∀ ω, ω ∈ A → ∀ u : ℝ≥0,
      u ≤ (17 / 16000 : ℝ≥0) →
      |B ω u| ≤ (1 / 4000 : ℝ))
    (hc : X.c = (2 : ℝ))
    (hDelta : ∀ m, m0 ≤ m →
      T + Δ m ≤ (17 / 16000 : ℝ≥0))
    (hεbound : (1 / 4000 : ℝ) ≤ ε)
    (v : ℕ → ℕ → ℝ) (M : ℕ → Ω → ℝ)
    (hMdef : ∀ m ω, ω ∈ A →
      let Y : ℕ → ℝ := fun i =>
        (1 / 8 : ℝ) + X.X (s m i) ω -
          rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
            (s m i) ω
      let Z : ℕ → ℝ := fun i =>
        X.X (s m (i + 1)) ω - X.X (s m i) ω -
          ((s m (i + 1) : ℝ) - (s m i : ℝ)) * X.c
      M m ω = (Finset.range (m + 1)).sum (fun i =>
        (if s m i < T then Real.exp (-(q * (s m i : ℝ))) *
          (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
        else 0) * Z i +
        (if s m i < T then (1 / 2 : ℝ) *
          Real.exp (-(q * (s m i : ℝ))) *
          (if Y i ∈ Icc a (5 / 44 : ℝ) then
            iteratedDeriv 2 w (Y i) else 0)
        else 0) * (Z i ^ 2 - v m i)))
    (N : Ω → ℝ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by
  have hCenteredTube : ∀ m, m0 ≤ m → ∀ ω, ω ∈ A →
      ∀ i, s m i ≤ T + Δ m →
        |X.X (s m i) ω - (s m i : ℝ) * X.c| ≤ ε := by
    intro m hm ω hω i hi
    have hiLong := hi.trans (hDelta m hm)
    have hb := hLongCentered ω hω (s m i) hiLong
    have hx := hLongSource ω hω (s m i) hiLong
    have heq : X.X (s m i) ω - (s m i : ℝ) * X.c =
        B ω (s m i) := by
      rw [hx, hc]
      ring
    rw [heq]
    exact hb.trans hεbound
  exact avram_gbB159_original_GH_stopped_L1_noise_control_from_centered_Brownian_tube
    X A hA m0 T s Δ hs hs0 hstep hX0
    q ε a hq hε w B hT hSource hCentered
    hCenteredTube v M hMdef N hNI hMI hL1
