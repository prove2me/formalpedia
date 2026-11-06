-- Prove2me | solution 1 for BianchiIX.eventually_partialCore_multiplier_formula
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:29:36.432524+00:00
-- url     : https://prove2.me/submissions/35633587-ad98-48dd-810b-4c5dcfef7fb0

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_eventually_forall_movingInterval
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_core_multipliers_of_regular
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreClockFactor (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) :
    ContDiffAt ℝ n (fun z : ProjectiveState =>
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  have hr2 : coreRadius (y 0) (y 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (coreRadius_pos hv))
  unfold coreClockFactor
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

end
end

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
open Set

private theorem BianchiIX.contDiffAt_projectiveOriginalFlow_two {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, t) := by
  have hparam : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    simpa only [Function.comp_def] using (contDiffAt_normalizedMaxCurve_two ht).comp (y, t) hparam
  simpa only [Function.comp_def, projectiveOriginalFlow] using
    (contDiffAt_toProjectiveState 2 (ne_of_gt hA)).comp (y, t) hN

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


/-- The integral factors describe the return map on an ordinary open germ, even at zero walls. -/
theorem solution {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContinuousAt τ y) (hpos : 0 < τ y)
    (hnear : ∀ᶠ x in 𝓝 y, ∀ t ∈ Icc 0 (τ x),
      t ∈ normalizedMaxDomain (fromProjectiveState x) 0 ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState x) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1) :
    ∀ᶠ x in 𝓝 y,
      projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
      projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1 := by
  have hbase := hnear.self_of_nhds
  have htube : ∀ᶠ x in 𝓝 y, ∀ t ∈ Icc 0 (τ x),
      let z := projectiveOriginalFlow x 0 t
      0 < z 2 ∧ projectiveStateDenom z ≠ 0 ∧
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0 := by
    apply eventually_forall_movingInterval hτ hpos
    intro t ht
    have hreg := coreRegion_clock_regular hk (hcore t ht)
    have hv := zero_lt_one.trans_le (hcore t ht).2.1
    have hf := (contDiffAt_projectiveOriginalFlow_two hD (hbase t ht).1 (hbase t ht).2).continuousAt
    have hV := (continuousAt_pi.mp hf 2).eventually (isOpen_Ioi.mem_nhds hv)
    have hden : ∀ᶠ p : ProjectiveState × ℝ in 𝓝 (y, t),
        0 < projectiveStateDenom (projectiveOriginalFlow p.1 0 p.2) :=
      (continuous_projectiveStateDenom.continuousAt.comp hf).eventually (isOpen_Ioi.mem_nhds hreg.1)
    have hfactor : ContinuousAt (fun z : ProjectiveState =>
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) (projectiveOriginalFlow y 0 t) :=
      (contDiffAt_projectiveCoreClockFactor 1 hv).continuousAt
    have hclockCont : ContinuousAt (fun p : ProjectiveState × ℝ =>
        let z := projectiveOriginalFlow p.1 0 p.2
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) (y, t) :=
      ContinuousAt.comp (f := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 0 p.2)
        (g := fun z : ProjectiveState => coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) hfactor hf
    have hclock : ∀ᶠ p : ProjectiveState × ℝ in 𝓝 (y, t),
        let z := projectiveOriginalFlow p.1 0 p.2
        0 < coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) :=
      hclockCont.eventually (isOpen_Ioi.mem_nhds hreg.2.1)
    filter_upwards [hV, hden, hclock] with p hpV hpD hpclock
    exact ⟨hpV, ne_of_gt hpD, ne_of_gt hpclock⟩
  have hden := continuous_projectiveStateDenom.continuousAt.eventually (isOpen_Ioi.mem_nhds hD)
  have hpositive := hτ.eventually (isOpen_Ioi.mem_nhds hpos)
  filter_upwards [hnear, htube, hden, hpositive, hhit] with x hx hreg hDx hτx hhitx
  have H := projectiveOriginalFlow_core_multipliers_of_regular hτx.le hDx
    (fun t ht => (hx t ht).1) (fun t ht => (hx t ht).2) hreg
  dsimp only at H
  rw [projectiveOriginalFlow_initial hDx, hhitx] at H
  simpa only [one_mul, partialCoreReturnMultiplier] using H
