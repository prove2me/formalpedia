-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_from_factorial_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:38:15.648787+00:00
-- url     : https://prove2.me/submissions/21da6dbb-b30e-4518-8de4-46b276d4c624

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_centered_count_L2_of_factorial_integrability
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_bounded_complete_integrability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Original intrinsic finite-band predictable L² isometry from physical factorial moments and independent future. -/
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
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
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
  letI : MeasurableSpace Ω := mΩ
  have hCountL2 (i : ℕ) : MemLp (fun ω => (N i ω).toReal - r i) 2 P :=
    avram_p4_g_isometry_centered_count_L2_of_factorial_integrability
      (fun ω => (N i ω).toReal) (r i) (hJ i) (hFactorialInt i)
  have hSecond (i : ℕ) :
      P[(fun ω => ((N i ω).toReal - r i) ^ 2) | 𝓕 (grid i)] =ᵐ[P]
        (fun _ => r i) := by
    have hSourceJ : ∀ ω, (N i ω).toReal =
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc (grid i) (grid (i + 1)) ×ˢ B i)).toReal := by
      intro ω
      rw [hActual i]
    exact avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
      X (grid i) (grid (i + 1)) (B i) (fun ω => (N i ω).toReal)
      hSourceJ (hJ i) (hFactorialInt i) (r i) (hRate i)
      (hFirst i) (hFactorial i)
      (mFuture i) (hFuture i) (hSqMeas i) (hIndependent i)
  exact avram_p4_g_isometry_original_finite_grid_bounded_complete_integrability
    X grid hGrid ε hε B hB hBand hν N hActual
    r hRate H D hD hH hHInf hPrefix hCountL2 hSecond n
