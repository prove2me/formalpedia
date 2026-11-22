-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_quadratic_L2_vanishing_implies_L1_via_Young
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:17:09.580839+00:00
-- url     : https://prove2.me/submissions/bdc854b9-7974-4975-b90d-bf817cc8a083

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_quadratic_absolute_Young_expected_bound
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℕ → Ω → ℝ)
    (hAbs : ∀ m, Integrable (fun ω => |U m ω|) P)
    (hSq : ∀ m, Integrable (fun ω => (U m ω) ^ 2) P)
    (hMom : Tendsto (fun m => ∫ ω, (U m ω) ^ 2 ∂P)
       atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, |U m ω| ∂P)
       atTop (𝓝 (0 : ℝ)) := by
  apply (tendsto_order).2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun m => by
      have h0 : 0 ≤ ∫ ω, |U m ω| ∂P :=
        integral_nonneg (fun ω => abs_nonneg _)
      linarith)
  · intro a ha
    have ha' : (0 : ℝ) < a / 2 := by linarith
    have hScaled :
        Tendsto
          (fun m => (∫ ω, (U m ω) ^ 2 ∂P) / (2 * a))
          atTop (𝓝 (0 : ℝ)) := by
      simpa using (hMom.div_const (2 * a))
    have hEventually :
        ∀ᶠ m in atTop,
          (∫ ω, (U m ω) ^ 2 ∂P) / (2 * a) < a / 2 :=
      hScaled.eventually_lt_const ha'
    filter_upwards [hEventually] with m hm
    have hYoung :=
      avram_ga_original_quadratic_absolute_Young_expected_bound
        P (U m) (hAbs m) (hSq m) a ha
    linarith
