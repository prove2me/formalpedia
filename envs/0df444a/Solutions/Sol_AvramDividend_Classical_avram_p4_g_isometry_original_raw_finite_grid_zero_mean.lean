-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_raw_finite_grid_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:08:06.693027+00:00
-- url     : https://prove2.me/submissions/1b797d26-3f9c-4724-953b-23d70b93cf97

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_weighted_L2_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

/-- Physical intrinsic predictable finite-grid compensated band sums have zero mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (C i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hMeas : ∀ i, Measurable (N i))
    (hRect : ∀ (i : ℕ) (A : Set Ω),
      MeasurableSet[𝓕 (grid i)] A →
      (∫⁻ ω in A, N i ω ∂P) =
        P A * ((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) 2 P)
    (n : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hcellInt (i : ℕ) :
      Integrable (fun ω => H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P :=
    (hHL2 i).integrable_mul (hCountL2 i)
  have hcellZero (i : ℕ) :
      (∫ ω, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal) ∂P) = 0 :=
    avram_p4_g_isometry_original_finite_band_weighted_L2_zero
      X (grid i) (grid (i + 1)) (hGrid i)
      ε hε (C i) (hC i) (hBand i) (hν i)
      (N i) (hActual i) (hMeas i) (hRect i)
      (H i) (hH i) (hHL2 i) (hCountL2 i)
  have hSumInt : Integrable (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P :=
    integrable_finset_sum (Finset.range n) (by
      intro i hi
      exact hcellInt i)
  refine ⟨hSumInt, ?_⟩
  rw [integral_finset_sum (Finset.range n) (by
    intro i hi
    exact hcellInt i)]
  simp only [hcellZero, Finset.sum_const_zero]
