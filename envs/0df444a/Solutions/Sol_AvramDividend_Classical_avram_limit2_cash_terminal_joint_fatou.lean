-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_cash_terminal_joint_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:16:50.174216+00:00
-- url     : https://prove2.me/submissions/04cf0d35-6e36-4667-8d83-5d93b6d60a3c

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Separate physical stopped-cash and surviving-terminal convergence give
    the precise combined Fatou liminf lower bound at positive horizons. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Cash Terminal : ℕ → Ω → ℝ)
    (cash terminal : Ω → ℝ)
    (hCash : ∀ᵐ ω ∂P,
      Tendsto (fun n => Cash n ω) atTop (nhds (cash ω)))
    (hTerminal : ∀ᵐ ω ∂P,
      Tendsto (fun n => Terminal n ω) atTop (nhds (terminal ω))) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal (cash ω + terminal ω) ≤
        liminf (fun n => ENNReal.ofReal (Cash n ω + Terminal n ω)) atTop := by
  filter_upwards [hCash, hTerminal] with ω hc ht
  have hReal : Tendsto (fun n => Cash n ω + Terminal n ω) atTop
      (nhds (cash ω + terminal ω)) := hc.add ht
  have hENN : Tendsto
      (fun n => ENNReal.ofReal (Cash n ω + Terminal n ω)) atTop
      (nhds (ENNReal.ofReal (cash ω + terminal ω))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hReal
  rw [hENN.liminf_eq]
