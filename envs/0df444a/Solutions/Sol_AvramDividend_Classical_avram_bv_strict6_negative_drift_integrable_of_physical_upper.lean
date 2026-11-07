-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_negative_drift_integrable_of_physical_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:36:50.048498+00:00
-- url     : https://prove2.me/submissions/89151cbe-b18d-404d-8477-3571e3f49146

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Original nonpositive drift L1 follows from its physical payoff domination. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (a : ℝ) (F M B E : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hM : Integrable M P) (hE : Integrable E P)
    (hBmeas : AEStronglyMeasurable B P)
    (hB : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hPath : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω + E ω) :
    Integrable B P := by
  have hC : Integrable (fun _ : Ω => |a|) P := integrable_const _
  have hDom : Integrable (fun ω => |a| + |M ω| + |E ω|) P :=
    (hC.add hM.abs).add hE.abs
  have hBound : ∀ᵐ ω ∂P,
      ‖B ω‖ ≤ ‖(|a| + |M ω| + |E ω| : ℝ)‖ := by
    filter_upwards [hF, hB, hPath] with ω hFn hBn hp
    have ha : a ≤ |a| := le_abs_self _
    have hm : M ω ≤ |M ω| := le_abs_self _
    have he : E ω ≤ |E ω| := le_abs_self _
    have hg : 0 ≤ |a| + |M ω| + |E ω| := by positivity
    have hbnd : -B ω ≤ |a| + |M ω| + |E ω| := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonpos hBn, abs_of_nonneg hg]
      using hbnd
  exact Integrable.mono hDom hBmeas hBound
