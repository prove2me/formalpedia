-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_original_stopped_physical_grid_L2_mean_zero_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:20:53.63538+00:00
-- url     : https://prove2.me/submissions/f568d3ae-275d-453f-ab91-db1d9a260256

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_rightcont_stopped_physical_grid_finite_L2
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_stopped_physical_grid_mean_zero_auto_count_L2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- The actual stopped negative-jump grid has both L² control and zero mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : ∀ i, X.ν (C i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) :
    let Z : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) *
          ((N i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C i)).toReal)
    MemLp Z 2 P ∧ (∫ ω, Z ω ∂P) = 0 := by
  constructor
  · exact avram_p4_s3_run1640_original_rightcont_stopped_physical_grid_finite_L2
      X T cut τ hτstop grid hGrid hTime ε hε C hC hBand hCut
      N hActual H hH hHL2 L hBound n
  · exact
      (avram_p4_s3_run1640_original_stopped_physical_grid_mean_zero_auto_count_L2
        X T cut τ hτstop grid hGrid hTime ε hε C hC
        hBand hCut hν N hActual H hH hHL2 n).2
