-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_factorial_future_auto_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:47:51.814237+00:00
-- url     : https://prove2.me/submissions/a54b7319-ef31-47e4-89d1-46f5b57dbdce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_from_factorial_future
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_prefix_adapted_from_endpoint_counts

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Original finite-grid isometry with adapted prefixes constructed from intrinsic endpoint-measurable counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
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
    (hJ : ∀ i, Integrable (fun ω => (N i ω).toReal) P)
    (hFactorialInt : ∀ i, Integrable (fun ω =>
      (N i ω).toReal * ((N i ω).toReal - 1)) P)
    (hFirst : ∀ i, (∫ ω, (N i ω).toReal ∂P) = r i)
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
  have hPrefix (i : ℕ) :
      StronglyMeasurable[𝓕 (grid i)]
        (fun ω => ∑ j ∈ Finset.range i, D j ω) :=
    avram_p4_g_isometry_prefix_adapted_from_endpoint_counts
      grid hGrid H (fun j ω => (N j ω).toReal)
      D r hD hH hCountEndpoint i
  exact avram_p4_g_isometry_original_finite_grid_from_factorial_future
    X grid hGrid ε hε B hB hBand hν N hActual
    r hRate H D hD hH hHInf hPrefix
    hJ hFactorialInt hFirst hFactorial
    mFuture hFuture hSqMeas hIndependent n
