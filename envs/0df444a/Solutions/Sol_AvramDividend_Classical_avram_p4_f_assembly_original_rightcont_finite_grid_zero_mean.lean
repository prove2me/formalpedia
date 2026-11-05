-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_rightcont_finite_grid_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:37:59.727243+00:00
-- url     : https://prove2.me/submissions/7ceaee68-3e5e-4dce-9ce0-4bcb9c592860

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_grid_zero_mean_from_source_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

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
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
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
  obtain ⟨Y, hYX, hYc, hYσ, hYν⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hActualY : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ Y.X u ω -
          Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          Y.X u ω - Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i) := by
    intro i
    simpa only [hYX] using hActual i
  have hνY : ∀ i, Y.ν (C i) < ⊤ := by
    intro i
    simpa only [hYν] using hν i
  have hCountL2Y : ∀ i, MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          Y.ν (C i)).toReal) 2 P := by
    intro i
    simpa only [hYν] using hCountL2 i
  simpa only [hYν] using
    (avram_p4_f_assembly_original_finite_grid_zero_mean_from_source_rate
      Y grid hGrid ε hε C hC hBand hνY
      N hActualY hMeas H hH hHL2 hCountL2Y n)
