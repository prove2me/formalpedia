-- Prove2me | solution 1 for BianchiIX.positiveIntegralClock_symm_zero
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:28:07.42828+00:00
-- url     : https://prove2.me/submissions/d33f29ab-fb68-42cd-ae36-608b650b1c39

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Theorems.Thm_BianchiIX_integralClock_initial
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
    (positiveIntegralClock hJ ho ha ht₀ hpos).symm 0 = t₀ := by
  let e := positiveIntegralClock hJ ho ha ht₀ hpos
  have he : e t₀ = 0 := integralClock_initial a t₀
  rw [← he]
  exact e.left_inv ht₀
