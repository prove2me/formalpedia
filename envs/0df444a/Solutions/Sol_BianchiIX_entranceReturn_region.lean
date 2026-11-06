-- Prove2me | solution 1 for BianchiIX.entranceReturn_region
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:14:55.767222+00:00
-- url     : https://prove2.me/submissions/894a6ed3-f847-4c2e-8178-70950d2fbc37

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_normalized_entrance_first_arrival
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entrance_initial_denom_pos {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) : 0 < projectiveStateDenom y := by
  have hr : |coreRadius (y 0) (y 2) - coreRadius (y 0) (y 2)| ≤ coreRadius (y 0) (y 2) / 100 := by
    rw [sub_self, abs_zero]
    linarith
  exact (entrance_denom_bounds hk (entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2.le⟩)
    hu ⟨hv.1.le, hv.2.le⟩ hw).1

end
end

/-- The named first-arrival map inherits the entire entrance region from the passage construction. -/
theorem solution {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    ∀ t ∈ Icc 0 (entranceReturnTime y),
      entranceRegion (coreRadius (y 0) (y 2)) (projectiveOriginalFlow y 0 t) := by
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc := fromProjectiveState_constraint hD.ne'
  have hinit : projectiveOriginalFlow y 0 0 = y := projectiveOriginalFlow_initial hD 0
  have hA : 0 < normalizedProjectiveRate (fromProjectiveState y) 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  obtain ⟨T, hT, hhit, hbefore, hreg, _⟩ := exists_normalized_entrance_first_arrival hc hk le_rfl hA
    (by change 1 ≤ projectiveOriginalFlow y 0 0 0; rwa [hinit])
    (by change coreRadius (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) = _; rw [hinit])
    (by change 0 ≤ projectiveOriginalFlow y 0 0 1 ∧ projectiveOriginalFlow y 0 0 1 ≤ _; rwa [hinit])
    (by change 0 < projectiveOriginalFlow y 0 0 2 ∧ projectiveOriginalFlow y 0 0 2 < _; rwa [hinit])
    (by change 0 ≤ projectiveOriginalFlow y 0 0 3 ∧ projectiveOriginalFlow y 0 0 3 ≤ _; rwa [hinit])
  have H := (entranceReturn_regular hk hm hu hv hw).1
  have hle : entranceReturnTime y ≤ T := H.1.2
    ⟨hT, normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le, hhit⟩
  have heq : entranceReturnTime y = T := by
    apply le_antisymm hle
    by_contra hn
    have hb := hbefore (entranceReturnTime y) ⟨H.1.1.1.le, lt_of_not_ge hn⟩
    have hh := H.1.1.2.2
    change projectiveOriginalFlow y 0 (entranceReturnTime y) 2 = 1 at hh
    change projectiveOriginalFlow y 0 (entranceReturnTime y) 2 < 1 at hb
    linarith
  rw [heq]
  exact fun t ht => (hreg t ht).2
