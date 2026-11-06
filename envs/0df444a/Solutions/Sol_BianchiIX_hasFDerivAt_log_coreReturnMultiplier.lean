-- Prove2me | solution 1 for BianchiIX.hasFDerivAt_log_coreReturnMultiplier
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:59:47.776303+00:00
-- url     : https://prove2.me/submissions/f3a97f52-f424-40bd-adb8-f76b9525c210

import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_hasFDerivAt_moving_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.log_coreFlowMultiplier (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    Real.log (coreFlowMultiplier y t₀ a b i) =
      ∫ t in a..b, coreOriginalLogRates (projectiveOriginalFlow y t₀ t) i :=
  Real.log_exp _

end
end

private theorem BianchiIX.contDiffAt_coreRadius_flow {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0) :
    ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
      (Y, t) := by
  have he := (contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).comp Y (contDiffAt_coreRadiusEntry 1 hk)
  have hp : ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
      (fromProjectiveState (coreRadiusEntry p.1), p.2)) (Y, t) :=
    (he.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hf := (normalizedMaxCurve_regular ht).2.comp (Y, t)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (f := fun p : CoreAngleState × ℝ => (fromProjectiveState (coreRadiusEntry p.1), p.2)) hp
  exact (contDiffAt_toProjectiveState 1 (ne_of_gt hA)).comp (Y, t) hf

/-- The endpoint motion is included in the derivative of the rescaled integrand. -/
theorem solution {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContDiffAt ℝ 1 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (i : Fin 2) :
    HasFDerivAt (fun Z => Real.log (coreReturnMultiplier τ Z i))
      (∫ s in (0 : ℝ)..1, (fderiv ℝ (coreRescaledLogRate τ i) (Y, s)).comp
        (ContinuousLinearMap.inl ℝ CoreAngleState ℝ)) Y := by
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) :
      ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
        coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2) i) (Y, t) := by
    have hreg := coreRegion_clock_regular hk (hcore t ht)
    have hc := contDiffAt_coreOriginalLogRates 1 (lt_of_lt_of_le zero_lt_one (hcore t ht).2.1)
      (ne_of_gt hreg.1) (ne_of_gt hreg.2.1)
    have hf := contDiffAt_coreRadius_flow (by linarith only [hk]) hD (hdom ht) (hA t ht)
    exact contDiffAt_pi.mp (hc.comp (Y, t) hf) i
  convert! hasFDerivAt_moving_intervalIntegral_of_contDiffAt hτ hpos hF using 1
  ext Z
  exact log_coreFlowMultiplier _ _ _ _ _
