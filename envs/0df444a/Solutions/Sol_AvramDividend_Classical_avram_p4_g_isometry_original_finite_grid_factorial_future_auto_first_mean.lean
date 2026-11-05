-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_factorial_future_auto_first_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:11:28.282249+00:00
-- url     : https://prove2.me/submissions/ced6e0e0-f6de-4689-a6b9-d373808e9725

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_band_L1_mean_auto_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_factorial_future_auto_prefix

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Physical original finite-grid factorial L2 isometry with automatic first moments and adapted prefixes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHInf : ∀ i, MemLp (H i) ⊤ P)
    (hCountEndpoint : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))]
      (fun ω => (N i ω).toReal))
    (hFactorialInt : ∀ i, Integrable (fun ω =>
      (N i ω).toReal * ((N i ω).toReal - 1)) P)
    (hFactorial : ∀ i, (∫ ω,
      (N i ω).toReal * ((N i ω).toReal - 1) ∂P) = (r i) ^ 2)
    (mFuture : ℕ → MeasurableSpace Ω)
    (hFuture : ∀ i, mFuture i ≤ mΩ)
    (hSqMeas : ∀ i, StronglyMeasurable[mFuture i]
      (fun ω => ((N i ω).toReal - r i) ^ 2))
    (hIndependent : ∀ i, Indep (mFuture i) (𝓕 (grid i)) P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMoment (i : ℕ) :
      Integrable (fun ω => (N i ω).toReal) P ∧
        (∫ ω, (N i ω).toReal ∂P) =
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal ∧
        (∀ᵐ ω ∂P, N i ω < ⊤) :=
    avram_p4_g_isometry_original_band_L1_mean_auto_compensator
      X (grid i) (grid (i + 1)) (hGrid i)
      ε hε (B i) (hB i) (hBand i) (hν i) (N i) (hActual i)
  have hJ (i : ℕ) : Integrable (fun ω => (N i ω).toReal) P :=
    (hMoment i).1
  have hFirst (i : ℕ) :
      (∫ ω, (N i ω).toReal ∂P) = r i := by
    rw [hRate i]
    exact (hMoment i).2.1
  exact avram_p4_g_isometry_original_finite_grid_factorial_future_auto_prefix
    X grid hGrid ε hε B hB hBand hν N hActual
    r hRate H D hD hH hHInf hCountEndpoint
    hJ hFactorialInt hFirst hFactorial mFuture hFuture hSqMeas hIndependent n
