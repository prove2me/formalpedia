-- Prove2me | solution 1 for AvramDividend.Classical.avram_0b16_nonnegative_payoff_certificate_forces_integrable_negative_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:03:13.246681+00:00
-- url     : https://prove2.me/submissions/15d46901-f834-4fb8-9c1c-88cab7223576

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
noncomputable section

/-- A nonnegative payoff forces L1 of a negative source in a finite-mean pathwise certificate. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F M B Err : Ω → ℝ) (a : ℝ)
    (hF : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hM : Integrable M P) (hErr : Integrable Err P)
    (hBmeas : AEStronglyMeasurable B P)
    (hBneg : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hPath : ∀ᵐ ω ∂P,
      F ω ≤ a + (M ω + B ω) + Err ω) :
    Integrable B P := by
  have hmajor : Integrable (fun ω => max a 0 + |M ω| + |Err ω|) P := by
    exact ((integrable_const _).add hM.abs).add hErr.abs
  refine Integrable.mono' hmajor hBmeas ?_
  filter_upwards [hF, hBneg, hPath] with ω hFω hBω hpath
  have hbabs : |B ω| = -B ω := abs_of_nonpos hBω
  have hmajorpos : 0 ≤ max a 0 + |M ω| + |Err ω| := by positivity
  rw [Real.norm_eq_abs, hbabs]
  have hmle : M ω ≤ |M ω| := le_abs_self _
  have hele : Err ω ≤ |Err ω| := le_abs_self _
  have hale : a ≤ max a 0 := le_max_left _ _
  linarith
