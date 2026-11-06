-- Prove2me | solution 1 for BianchiIX.exists_normalized_entrance_first_arrival
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:07:35.083321+00:00
-- url     : https://prove2.me/submissions/dec5e400-acc2-4f3f-b8ac-0dfb2efa5b92

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Theorems.Thm_BianchiIX_exists_normalized_entrance_arrival
import Theorems.Thm_BianchiIX_normalized_entrance_active_strictMono
import Theorems.Thm_BianchiIX_normalized_entrance_decay
import Theorems.Thm_BianchiIX_normalized_entrance_radius_improves
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    1 ≤ Y s 0 → coreRadius (Y s 0) (Y s 2) = k →
    (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
    (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
    ∃ t > s, Y t 2 = 1 ∧ (∀ r ∈ Ico s t, Y r 2 < 1) ∧
      (∀ r ∈ Icc s t, 1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r)) ∧
      (∀ r ∈ Icc s t, |coreRadius (Y r 0) (Y r 2) - k| < k / 200 ∧
        Y r 1 ≤ Y s 1 * Real.exp (-(1 + k / 3) * (Real.log (Y r 2) - Real.log (Y s 2))) ∧
        Y r 3 ≤ Y s 3 * Real.exp (-(1 + 1 / k) * (Real.log (Y r 2) - Real.log (Y s 2)))) := by
  intro Y hm hR hu hv hw
  obtain ⟨t, hst, ht, hregion⟩ := exists_normalized_entrance_arrival hc hk hs hA hm hR hu hv hw
  have hK : 0 < k + 1 := by linarith
  have hpos : 0 < 1 / (2 * (k + 1) ^ 2) := by positivity
  have hAp (r : ℝ) (hr : r ∈ Icc s t) : 0 < normalizedProjectiveRate x t₀ r := hpos.trans_le (hregion r hr).1
  have hmono := normalized_entrance_active_strictMono hc hk hs hst.le hAp (fun r hr => (hregion r hr).2) hv.1
  refine ⟨t, hst, ht, ?_, hregion, ?_⟩
  · intro r hr
    rw [← ht]
    exact hmono ⟨hr.1, hr.2.le⟩ ⟨hst.le, le_rfl⟩ hr.2
  · intro r hr
    have hsub : Icc s r ⊆ Icc s t := fun b hb => ⟨hb.1, hb.2.trans hr.2⟩
    exact ⟨(normalized_entrance_radius_improves hc hk hs hr.1 (fun b hb => hAp b (hsub hb))
      (fun b hb => (hregion b (hsub hb)).2) hv.1 hR).2,
      normalized_entrance_decay hc hk hs hst.le hAp (fun b hb => (hregion b hb).2) hv.1 r hr⟩
