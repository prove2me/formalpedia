-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb55_original_integrable_positive_error_ruin_mask_dominated_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:52:05.588541+00:00
-- url     : https://prove2.me/submissions/e0692ff3-683a-41ba-92be-3ed2dbe44150

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (E : ℕ → Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A)
    (hE : ∀ n, Integrable (fun ω => max (E n ω) (0 : ℝ)) P)
    (K : Ω → ℝ) (hKI : Integrable K P)
    (hBound : ∀ n, ∀ᵐ ω ∂P, ‖if ω ∈ A then (0 : ℝ)
       else max (E n ω) 0‖ ≤ K ω)
    (hLim : ∀ᵐ ω ∂P, Tendsto (fun n => if ω ∈ A then (0 : ℝ)
       else max (E n ω) 0) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ∫ ω, (if ω ∈ A then (0 : ℝ)
       else max (E n ω) 0) ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hAE (n : ℕ) : AEStronglyMeasurable
      (fun ω : Ω => if ω ∈ A then (0 : ℝ) else max (E n ω) 0) P := by
    have hi := (hE n).aestronglyMeasurable.indicator hA.compl
    have hEq :
        (Aᶜ).indicator (fun ω => max (E n ω) (0 : ℝ)) =
        (fun ω => if ω ∈ A then (0 : ℝ) else max (E n ω) 0) := by
      funext ω
      by_cases hw : ω ∈ A <;> simp [Set.indicator, hw]
    simpa only [hEq] using hi
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence K hAE hKI hBound hLim)
