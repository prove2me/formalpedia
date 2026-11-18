-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_positive_event_stopped_GH_L1_refutes_fixedband_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:16:29.264969+00:00
-- url     : https://prove2.me/submissions/6f6ad8a8-a9f4-4c47-90d2-1d9160503208

import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB184_uniform_mesh_gaussian_GH_L1_bounded_long_source_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
/-- Original stopped G/H L1 bounds contradict positive-drift uncharged Gaussian cash budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A)
    (hPos : 0 < P A)
    (m0 : ℕ) (T : ℝ≥0) (s : ℕ → ℕ → ℝ≥0)
    (Δ : ℕ → ℝ≥0)
    (hs : ∀ m, Monotone (s m))
    (hs0 : ∀ m, s m 0 = 0)
    (hstep : ∀ m i, s m (i + 1) = s m i + Δ m)
    (hX0 : ∀ ω, X.X 0 ω = 0)
    (q ε a : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hεExact : ε = (1 / 4000 : ℝ))
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
    (n : ℕ)
    (hUniform : ∀ m, Δ m =
      (n : ℝ≥0) / ((m : ℝ≥0) + 1))
    (hM0 : 16000 * n ≤ m0 + 1)
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
      atTop (𝓝 (0 : ℝ)))
    (hBudget : ∀ᵐ ω ∂(P.restrict A), Real.exp (-(1 / 100000 : ℝ)) *
        (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
      (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal - (3 / 16 : ℝ) ≤ N ω + (1 / 1936 : ℝ)) :
    False := by
  have hBound :=
    avram_gbB184_uniform_mesh_gaussian_GH_L1_bounded_long_source_tube
      X A hA m0 T s Δ hs hs0 hstep hX0
      q ε a hq hε w B hT hSource hCentered
      hLongSource hLongCentered hc
      n hUniform hM0 hεbound
      v M hMdef N hNI hMI hL1
  have hNoise : ∀ᵐ ω ∂(P.restrict A),
      |N ω| ≤ (1 / 4000 : ℝ) := by
    filter_upwards [hBound] with ω hω
    simpa only [hεExact] using hω
  exact avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
    X A hA hPos B hSource hCentered
    N hNoise hBudget
