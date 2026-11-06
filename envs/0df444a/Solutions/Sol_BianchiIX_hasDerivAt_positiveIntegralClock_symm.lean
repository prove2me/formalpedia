-- Prove2me | solution 1 for BianchiIX.hasDerivAt_positiveIntegralClock_symm
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:19:52.936619+00:00
-- url     : https://prove2.me/submissions/50731910-23dc-480c-9836-363db63f73b9

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology


theorem solution {J : Set ℝ} {a : ℝ → ℝ} {t₀ τ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t)
    (hτ : τ ∈ (positiveIntegralClock hJ ho ha ht₀ hpos).target) :
    HasDerivAt (positiveIntegralClock hJ ho ha ht₀ hpos).symm
      (1 / a ((positiveIntegralClock hJ ho ha ht₀ hpos).symm τ)) τ := by
  let e := positiveIntegralClock hJ ho ha ht₀ hpos
  have ht : e.symm τ ∈ J := e.map_target hτ
  simpa only [one_div] using e.hasDerivAt_symm hτ (ne_of_gt (hpos _ ht))
    (hasStrictDerivAt_integralClock hJ ho ha ht₀ ht).hasDerivAt
