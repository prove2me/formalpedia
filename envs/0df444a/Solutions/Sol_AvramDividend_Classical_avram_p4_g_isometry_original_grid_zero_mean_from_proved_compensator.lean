-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_grid_zero_mean_from_proved_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:32:22.577402+00:00
-- url     : https://prove2.me/submissions/ceb94130-e285-4854-9248-bb358f55b777

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_finite_grid_zero_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

/-- Finite-grid centred physical jump count sum, using the proved original rectangle law in each block. -/
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
  have hRect : ∀ (i : ℕ) (A : Set Ω),
      MeasurableSet[𝓕 (grid i)] A →
      (∫⁻ ω in A, N i ω ∂P) =
        P A * ((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (C i) := by
    intro i A hA
    simpa only [hActual i] using
      (avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
        X (grid i) (grid (i + 1)) (hGrid i) A hA (C i) (hC i))
  exact avram_p4_g_isometry_original_raw_finite_grid_zero_mean
    X grid hGrid ε hε C hC hBand hν N hActual hMeas hRect
    H hH hHL2 hCountL2 n
