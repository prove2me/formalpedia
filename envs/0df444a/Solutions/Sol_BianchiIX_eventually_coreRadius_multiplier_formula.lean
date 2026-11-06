-- Prove2me | solution 1 for BianchiIX.eventually_coreRadius_multiplier_formula
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:01:50.590218+00:00
-- url     : https://prove2.me/submissions/d9fa9ab8-8b98-42bf-8727-63bebae5db7b

import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreRadius_flow_regular
import Theorems.Thm_BianchiIX_eventually_forall_movingInterval
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_core_multipliers_of_regular
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
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

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

end
end

theorem solution {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContinuousAt τ Y) (hpos : 0 < τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (hhit : ∀ᶠ Z in 𝓝 Y, projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1) :
    ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1 := by
  have htube : ∀ᶠ Z in 𝓝 Y, ∀ t ∈ Icc 0 (τ Z),
      t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Z)) 0 t 0 ∧
      let z := projectiveOriginalFlow (coreRadiusEntry Z) 0 t
      0 < z 2 ∧ projectiveStateDenom z ≠ 0 ∧
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0 := by
    apply eventually_forall_movingInterval hτ hpos
    intro t ht
    have hreg := coreRegion_clock_regular hk (hcore t ht)
    have hv := lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
    obtain ⟨hnear, hf⟩ := coreRadius_flow_regular (by linarith only [hk]) hD (hdom ht) (hA t ht)
    have hV := (continuousAt_pi.mp hf 2).eventually (isOpen_Ioi.mem_nhds hv)
    have hden : ∀ᶠ p : CoreAngleState × ℝ in 𝓝 (Y, t),
        0 < projectiveStateDenom (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2) :=
      (continuous_projectiveStateDenom.continuousAt.comp hf).eventually (isOpen_Ioi.mem_nhds hreg.1)
    have hfactor : ContinuousAt (fun z : ProjectiveState =>
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3))
        (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) :=
      (contDiffAt_projectiveCoreClockFactor 1 hv).continuousAt
    have hclockCont : ContinuousAt (fun p : CoreAngleState × ℝ =>
        let z := projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) (Y, t) :=
      ContinuousAt.comp (f := fun p : CoreAngleState × ℝ =>
        projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
        (g := fun z : ProjectiveState => coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) hfactor hf
    have hclock : ∀ᶠ p : CoreAngleState × ℝ in 𝓝 (Y, t),
        let z := projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2
        0 < coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) :=
      hclockCont.eventually (isOpen_Ioi.mem_nhds hreg.2.1)
    filter_upwards [hnear, hV, hden, hclock] with p hp hpV hpD hpclock
    exact ⟨hp.1, hp.2, hpV, ne_of_gt hpD, ne_of_gt hpclock⟩
  have hentry := (contDiffAt_coreRadiusEntry 1 (by linarith only [hk])).continuousAt
  have hden := (continuous_projectiveStateDenom.continuousAt.comp hentry).eventually
    (isOpen_Ioi.mem_nhds hD)
  have hpositive := hτ.eventually (isOpen_Ioi.mem_nhds hpos)
  filter_upwards [htube, hden, hpositive, hhit] with Z hZ hDZ hτZ hhitZ
  have H := projectiveOriginalFlow_core_multipliers_of_regular hτZ.le hDZ
    (fun t ht => (hZ t ht).1) (fun t ht => (hZ t ht).2.1) (fun t ht => (hZ t ht).2.2)
  dsimp only at H
  rw [projectiveOriginalFlow_initial hDZ, hhitZ] at H
  simpa [coreRadiusEntry, coreReturnMultiplier] using H
