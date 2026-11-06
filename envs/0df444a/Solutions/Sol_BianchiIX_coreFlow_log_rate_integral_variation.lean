-- Prove2me | solution 1 for BianchiIX.coreFlow_log_rate_integral_variation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:04:29.09794+00:00
-- url     : https://prove2.me/submissions/9eaf91b6-1859-4e25-88e1-27e8686c511a

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreLinearization
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreLogIntegralVariation
import Theorems.Thm_BianchiIX_contDiffAt_coreLogRates_joint
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coreLogBoundary
import Theorems.Thm_BianchiIX_hasDerivAt_coreProjectedFlowVariation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
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

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.integral_eq_projected_add_boundary {g h B : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) (hh : ContinuousOn h (Icc a b))
    (hB : ∀ t ∈ Icc a b, HasDerivAt B (g t - h t) t) :
    (∫ t in a..b, g t) = (∫ t in a..b, h t) + B b - B a := by
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hB t (uIcc_of_le hab ▸ ht))
    ((hg.sub hh).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable_of_Icc hab) (hh.intervalIntegrable_of_Icc hab)] at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreAngle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n projectiveCoreAngle y := by
  have hv0 := ne_of_gt hv
  unfold projectiveCoreAngle coreAngle
  fun_prop

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

private theorem BianchiIX.contDiffAt_toCoreAngleState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n toCoreAngleState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toCoreAngleState] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreOriginalClockRate (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) (hD : projectiveStateDenom y ≠ 0) :
    ContDiffAt ℝ n coreOriginalClockRate y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  have hr2 : coreRadius (y 0) (y 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (coreRadius_pos hv))
  have hden := (contDiff_projectiveStateDenom n).contDiffAt (x := y)
  unfold coreOriginalClockRate coreClockFactor
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreAuxiliary_projective_clockFactor {y : ProjectiveState} (hv : 0 < y 2) :
    coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 =
      coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  change coreClockFactor (coreRadius (y 0) (y 2)) (y 1)
    (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) = _
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]

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

private theorem BianchiIX.continuousAt_coreLogRates_stateDifferential {z : ℝ} {Y : CoreAngleState}
    (hr : Y 0 ≠ 0) (hd : coreAuxiliary z Y 1 ≠ 0) :
    ContinuousAt (fun p : ℝ × CoreAngleState => fderiv ℝ (coreLogRates p.1) p.2) (z, Y) := by
  have hp : ContDiffAt ℝ 1
      (fun q : (ℝ × CoreAngleState) × CoreAngleState => (q.1.1, q.2)) ((z, Y), Y) :=
    (contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd
  have hL := (contDiffAt_coreLogRates_joint 1 z hr hd).comp ((z, Y), Y)
    (f := fun q : (ℝ × CoreAngleState) × CoreAngleState => (q.1.1, q.2)) hp
  exact (hL.fderiv (m := 0) contDiffAt_snd (by norm_num)).continuousAt

theorem solution {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (w : ProjectiveState) (i : Fin 2) :
    let β := projectiveOriginalFlow y t₀
    let ξ := fun t => coreProjectedFlowVariation y t₀ t w
    (∫ t in a..b, (fderiv ℝ coreOriginalLogRates (β t) (projectiveFlowDifferential y t₀ t w)) i) =
      (∫ t in a..b, coreOriginalClockRate (β t) *
        (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t)) (ξ t)) i) +
      coreLogBoundary y t₀ b w i - coreLogBoundary y t₀ a w i := by
  intro β ξ
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hv (t : ℝ) (ht : t ∈ Icc a b) : 0 < β t 2 := lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hreg (t : ℝ) (ht : t ∈ Icc a b) := coreRegion_clock_regular hk (hcore t ht)
  apply integral_eq_projected_add_boundary hab
  · intro t ht
    have hdiff := (contDiffAt_coreOriginalLogRates 1 (hv t ht) (ne_of_gt (hreg t ht).1)
      (ne_of_gt (hreg t ht).2.1)).continuousAt_fderiv (by norm_num)
    have hvar := (hasDerivAt_projectiveFlowDifferential_apply hD (hdom ht) (hA t ht) w).continuousAt
    exact (continuousAt_pi.mp ((hdiff.comp (hflow t ht).continuousAt).clm_apply hvar) i).continuousWithinAt
  · intro t ht
    have hd : coreAuxiliary (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) 1 ≠ 0 := by
      rw [coreAuxiliary_projective_clockFactor (hv t ht)]
      exact ne_of_gt (hreg t ht).2.1
    have hdiff := continuousAt_coreLogRates_stateDifferential (ne_of_gt (coreRadius_pos (hv t ht))) hd
    have hp := ((contDiffAt_projectiveCoreAngle 1 (hv t ht)).continuousAt.comp (hflow t ht).continuousAt).prodMk
      ((contDiffAt_toCoreAngleState 1 (hv t ht)).continuousAt.comp (hflow t ht).continuousAt)
    have hvar := (hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hv t ht)
      (ne_of_gt (hreg t ht).2.1) w).continuousAt
    have hcomp := hdiff.comp
      (g := fun p : ℝ × CoreAngleState => fderiv ℝ (coreLogRates p.1) p.2)
      (f := fun s : ℝ => (projectiveCoreAngle (β s), toCoreAngleState (β s))) hp
    have hvalue := continuousAt_pi.mp (hcomp.clm_apply hvar) i
    have hrate := (contDiffAt_coreOriginalClockRate 1 (hv t ht) (ne_of_gt (hreg t ht).1)).continuousAt.comp
      (hflow t ht).continuousAt
    exact (hrate.mul hvalue).continuousWithinAt
  · intro t ht
    exact hasDerivAt_coreLogBoundary hD (hdom ht) (hA t ht) (hv t ht) (ne_of_gt (hreg t ht).2.1) w i
