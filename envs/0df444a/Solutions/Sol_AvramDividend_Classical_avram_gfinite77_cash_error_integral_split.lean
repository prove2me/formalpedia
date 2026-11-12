-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite77_cash_error_integral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:08:22.972795+00:00
-- url     : https://prove2.me/submissions/79c61742-60cc-4c93-bc40-87c347ee2e72

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Split an expected positive Gaussian cash residual into the source error
    and the mesh approximation error. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (f g : Ω → ℝ)
    (hf : IntegrableOn (fun ω => max (f ω) 0) A P)
    (hg : IntegrableOn (fun ω => max (g ω) 0) A P)
    (hs : IntegrableOn (fun ω => max (f ω + g ω) 0) A P) :
    (∫ ω in A, max (f ω + g ω) 0 ∂P) ≤
      (∫ ω in A, max (f ω) 0 ∂P) +
        (∫ ω in A, max (g ω) 0 ∂P) := by
  calc
    (∫ ω in A, max (f ω + g ω) 0 ∂P) ≤
        (∫ ω in A, max (f ω) 0 + max (g ω) 0 ∂P) := by
      apply integral_mono hs (hf.add hg)
      intro ω
      simp only [Pi.add_apply]
      have h₁ : f ω ≤ max (f ω) 0 := le_max_left _ _
      have h₂ : g ω ≤ max (g ω) 0 := le_max_left _ _
      have h₃ : (0 : ℝ) ≤ max (f ω) 0 := le_max_right _ _
      have h₄ : (0 : ℝ) ≤ max (g ω) 0 := le_max_right _ _
      apply max_le
      · linarith
      · linarith
    _ = (∫ ω in A, max (f ω) 0 ∂P) +
          (∫ ω in A, max (g ω) 0 ∂P) := by
      exact integral_add hf hg
