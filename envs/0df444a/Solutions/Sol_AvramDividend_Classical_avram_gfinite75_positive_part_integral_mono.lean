-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite75_positive_part_integral_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:39:57.75676+00:00
-- url     : https://prove2.me/submissions/28cae063-a52e-4de5-880b-4f19300df921

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A pointwise almost-everywhere cash-residual bound gives an expected
    positive-residual bound once both positive parts are integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (f g : Ω → ℝ)
    (hf : IntegrableOn (fun ω => max (f ω) 0) A P)
    (hg : IntegrableOn (fun ω => max (g ω) 0) A P)
    (hfg : ∀ᵐ ω ∂P.restrict A, f ω ≤ g ω) :
    (∫ ω in A, max (f ω) 0 ∂P) ≤
      (∫ ω in A, max (g ω) 0 ∂P) := by
  apply integral_mono_ae hf hg
  filter_upwards [hfg] with ω hω
  exact max_le_max hω le_rfl
