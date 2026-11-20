-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_centred_source_signed_grid_bias_expected_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:07:48.262189+00:00
-- url     : https://prove2.me/submissions/0ce1c232-d932-4d49-93e0-877524ba6707

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Source M Q : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hM : ∀ j, Integrable (M j) P)
    (hQ : ∀ j, Integrable (Q j) P)
    (hMzero : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hQmean : ∀ j, (∫ ω, Q j ω ∂P) ≤ 0)
    (hSource : ∀ j ω,
      Source j ω = M j ω + Q j ω + bias j) :
    ∀ j, (∫ ω, Source j ω ∂P) ≤ bias j := by
  intro j
  have hfun : Source j = fun ω => M j ω + Q j ω + bias j := by
    funext ω
    exact hSource j ω
  rw [hfun]
  have hpair : Integrable (fun ω => M j ω + Q j ω) P :=
    (hM j).add (hQ j)
  have hEq :
      (∫ ω, M j ω + Q j ω + bias j ∂P) =
      (∫ ω, M j ω ∂P) + (∫ ω, Q j ω ∂P) + bias j := by
    rw [integral_add hpair (integrable_const (bias j))]
    rw [integral_add (hM j) (hQ j)]
    simp
  rw [hEq, hMzero j]
  linarith [hQmean j]
