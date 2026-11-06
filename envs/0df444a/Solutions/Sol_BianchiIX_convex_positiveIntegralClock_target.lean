-- Prove2me | solution 1 for BianchiIX.convex_positiveIntegralClock_target
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:20:28.833763+00:00
-- url     : https://prove2.me/submissions/228c64f1-f012-4a86-a0e4-4ebc3ce4aa82

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology


theorem solution {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    Convex ℝ (positiveIntegralClock hJ ho ha ht₀ hpos).target := by
  let e := positiveIntegralClock hJ ho ha ht₀ hpos
  rw [← e.image_source_eq_target]
  exact (hJ.isPreconnected.image e e.continuousOn).convex
