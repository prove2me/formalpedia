-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_global_centered_L2_grid_has_L1_limit_on_future_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:44:22.745299+00:00
-- url     : https://prove2.me/submissions/727ff96d-c1f5-45ca-84bc-24aa661783fe

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_avram_gb36_L2_cauchy_eventwise_centred_L1_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped Topology
open MeasureTheory Filter Set AvramDividend.Classical
open scoped ENNReal
noncomputable section
/-- Global centred L2 Gaussian grid transfers its L1 limit to future events. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (M : ℕ → Ω → ℝ)
    (hMLp : ∀ m, MemLp (M m) 2 P)
    (hMInt : ∀ m, Integrable (M m) P)
    (hCauchy : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (M nm.1 - M nm.2) 2 P) atTop (𝓝 (0 : ℝ≥0∞)))
    (hMeanGlobal : Tendsto (fun m => ∫ ω, M m ω ∂P)
      atTop (𝓝 (0 : ℝ)))
    (A : Set Ω) (hA : MeasurableSet A) :
    ∃ N : Ω → ℝ, Integrable N P ∧
      (∫ ω, N ω ∂P) = 0 ∧
      Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨N, hNInt, hZero, hL1⟩ :=
    avram_gb36_L2_cauchy_eventwise_centred_L1_limit
      P Set.univ M hMLp hCauchy (by simpa using hMeanGlobal)
  have hL1Global :
      Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hL1
  have hUpper (m : ℕ) :
      (∫ ω in A, |N ω - M m ω| ∂P) ≤
      ∫ ω, |N ω - M m ω| ∂P :=
    setIntegral_le_integral ((hNInt.sub (hMInt m)).abs)
      (Eventually.of_forall (fun ω => abs_nonneg _))
  have hLower (m : ℕ) :
      0 ≤ ∫ ω in A, |N ω - M m ω| ∂P :=
    integral_nonneg (fun ω => abs_nonneg _)
  refine ⟨N, hNInt, ?_, ?_⟩
  · simpa using hZero
  · exact squeeze_zero hLower hUpper hL1Global
