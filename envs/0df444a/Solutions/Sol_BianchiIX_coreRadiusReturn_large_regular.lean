-- Prove2me | solution 1 for BianchiIX.coreRadiusReturn_large_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:32:13.221193+00:00
-- url     : https://prove2.me/submissions/903cd793-038c-447d-9e0b-ce35a515b014

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_exists_large_core_radius_arrival
import Theorems.Thm_BianchiIX_exists_large_core_traversal
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRegion_clock_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    0 < projectiveStateDenom y ∧
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ∧
        0 < coreOriginalClockRate y := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hD := coreBootstrap_denom_lower (m := y 0) (v := y 2) hk hu hw
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have hrate := coreBootstrap_original_clock_lower hk hr (zero_le_one.trans hy.2.1) hu hw
  exact ⟨lt_of_lt_of_le (by norm_num) hD, lt_of_lt_of_le (by norm_num) hd,
    lt_of_lt_of_le (one_div_pos.mpr hk0) hrate⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_region {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    coreRegion (Y 0) (coreRadiusEntry Y) := by
  have hR := coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)
  have he := coreRadius_sq (coreRadiusEntry Y 0) (coreRadiusEntry Y 2)
  rw [hR] at he
  refine ⟨?_, le_rfl, hu, ?_⟩
  · rw [← he, sub_self, abs_zero]
    norm_num
  · simpa [coreRadiusEntry] using hw

end
end

private theorem BianchiIX.coreRadiusReturnTime_eq_of_first {Y : CoreAngleState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T)
    (hdom : T ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0) :
    coreRadiusReturnTime Y = T := by
  apply IsLeast.csInf_eq
  exact ⟨⟨hT.1.1, hdom, hT.1.2⟩, fun t ht => hT.2 ⟨ht.1, ht.2.2⟩⟩

private theorem BianchiIX.coreRadiusReturnTime_eventuallyEq {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hτ : ∀ᶠ Z in 𝓝 Y,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
        τ Z ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0) :
    coreRadiusReturnTime =ᶠ[𝓝 Y] τ :=
  hτ.mono fun _ h => coreRadiusReturnTime_eq_of_first h.1 h.2

/-- The compact-core and large-core constructions use the same actual first return. -/
theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 coreRadiusReturnTime Y ∧
      ContDiffAt ℝ 1 (coreReturnState coreRadiusReturnTime) Y ∧
      (∀ᶠ Z in 𝓝 Y,
        IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1}
          (coreRadiusReturnTime Z)) := by
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hcF, _⟩ := exists_large_core_radius_arrival hk hu hw
  have heq := coreRadiusReturnTime_eventuallyEq (hnear.mono fun Z h =>
    ⟨h.1, (h.2 (τ Z) ⟨h.1.1.1.le, le_rfl⟩).1⟩)
  have hstate : coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y] coreReturnState τ := by
    filter_upwards [heq] with Z hZ
    simp only [coreReturnState, hZ]
  have htime : coreRadiusReturnTime Y = T := heq.self_of_nhds.trans hτ
  refine ⟨?_, hcτ.congr_of_eventuallyEq heq, hcF.congr_of_eventuallyEq hstate, ?_⟩
  · obtain ⟨S, _, hS, hcore, _, _, hneg, _⟩ := exists_large_core_traversal hk hu hw
    have hST : S = T := hS.unique hfirst
    subst S
    have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
    have hc := fromProjectiveState_constraint hD.ne'
    have hdom (t : ℝ) (ht : 0 ≤ t) :
        t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 :=
      normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht
    change coreRadiusReturnValid Y
    dsimp only [coreRadiusReturnValid]
    rw [htime]
    refine ⟨⟨⟨hT, hdom T hT.le, hfirst.1.2⟩,
      fun t ht => hfirst.2 ⟨ht.1, ht.2.2⟩⟩,
      fun t ht => ⟨hdom t ht.1, (hcore t ht).1⟩, ?_, ?_⟩
    · intro t ht
      have hv : 1 ≤ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 :=
        (hcore t ⟨ht.1.le, ht.2.le⟩).2.2.1
      exact lt_of_le_of_ne hv (fun he => (not_le_of_gt ht.2) (hfirst.2 ⟨ht.1, he.symm⟩))
    · have hA := (hcore T ⟨hT.le, le_rfl⟩).1
      have hd := ((contDiffAt_projectiveActiveWall 1 hA.ne').differentiableAt
        (by norm_num)).hasFDerivAt.comp_hasDerivAt T (hasDerivAt_normalizedMaxCurve (hdom T hT.le))
      change HasDerivAt (fun t => projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2)
        (normalizedEventRate projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) 0 T) T at hd
      rwa [← hd.deriv]
  · filter_upwards [hnear, heq] with Z hZ ht
    rw [ht]
    exact hZ.1
