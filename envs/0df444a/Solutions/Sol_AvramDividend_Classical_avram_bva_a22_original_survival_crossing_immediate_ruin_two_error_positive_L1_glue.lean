-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_survival_crossing_immediate_ruin_two_error_positive_L1_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:05:41.57366+00:00
-- url     : https://prove2.me/submissions/0d6946fb-523e-42e5-bc68-2a357988a049

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Err ErrSurvival ErrCrossing : ℕ → Ω → ℝ)
    (Surv Cross : Ω → Prop)
    (hI : ∀ m, Integrable (fun ω => max (Err m ω) 0) P)
    (hIS : ∀ m, Integrable (fun ω => max (ErrSurvival m ω) 0) P)
    (hIC : ∀ m, Integrable (fun ω => max (ErrCrossing m ω) 0) P)
    (hS : ∀ m, ∀ᵐ ω ∂P, Surv ω →
      Err m ω ≤ max (ErrSurvival m ω) 0)
    (hC : ∀ m, ∀ᵐ ω ∂P, Cross ω →
      Err m ω ≤ max (ErrCrossing m ω) 0)
    (hZ : ∀ m, ∀ᵐ ω ∂P, ¬ Surv ω → ¬ Cross ω → Err m ω ≤ 0)
    (hLS : Tendsto (fun m => ∫ ω, max (ErrSurvival m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hLC : Tendsto (fun m => ∫ ω, max (ErrCrossing m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hPoint : ∀ m, ∀ᵐ ω ∂P,
      max (Err m ω) 0 ≤
        max (ErrSurvival m ω) 0 + max (ErrCrossing m ω) 0 := by
    intro m
    filter_upwards [hS m, hC m, hZ m] with ω hs hc hz
    have hns : 0 ≤ max (ErrSurvival m ω) 0 := le_max_right _ _
    have hnc : 0 ≤ max (ErrCrossing m ω) 0 := le_max_right _ _
    have he : Err m ω ≤
        max (ErrSurvival m ω) 0 + max (ErrCrossing m ω) 0 := by
      by_cases hsurv : Surv ω
      · exact (hs hsurv).trans (le_add_of_nonneg_right hnc)
      · by_cases hcross : Cross ω
        · exact (hc hcross).trans (le_add_of_nonneg_left hns)
        · exact (hz hsurv hcross).trans (add_nonneg hns hnc)
    exact max_le he (add_nonneg hns hnc)
  have hLow : ∀ m, 0 ≤ ∫ ω, max (Err m ω) 0 ∂P :=
    fun m => integral_nonneg (fun ω => le_max_right _ _)
  have hUpper : ∀ m,
      (∫ ω, max (Err m ω) 0 ∂P) ≤
      (∫ ω, max (ErrSurvival m ω) 0 +
        max (ErrCrossing m ω) 0 ∂P) := by
    intro m
    exact integral_mono_ae (hI m) ((hIS m).add (hIC m)) (hPoint m)
  have hSum : Tendsto
      (fun m => ∫ ω, max (ErrSurvival m ω) 0 +
        max (ErrCrossing m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    have heq :
        (fun m => ∫ ω, max (ErrSurvival m ω) 0 +
          max (ErrCrossing m ω) 0 ∂P) =
        (fun m => (∫ ω, max (ErrSurvival m ω) 0 ∂P) +
          (∫ ω, max (ErrCrossing m ω) 0 ∂P)) := by
      funext m
      exact integral_add (hIS m) (hIC m)
    rw [heq]
    simpa only [add_zero] using hLS.add hLC
  exact squeeze_zero hLow hUpper hSum
