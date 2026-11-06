-- Prove2me | solution 1 for BianchiIX.coreProjectedFlowVariation_strong_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:03:49.183481+00:00
-- url     : https://prove2.me/submissions/62405eb8-17f9-4d1a-8eba-03d95b16ce18

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreLinearization
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreRegion_strong_forcing
import Theorems.Thm_BianchiIX_coreWeightedJacobian_mulVec
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_hasDerivAt_coreProjectedFlowVariation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_prefix_contraction
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
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
open Set

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

/-- The strong component of the genuine flow derivative, estimated without inverting the angular clock. -/
theorem solution {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    ∀ t ∈ Icc a b,
      let θ := fun s => projectiveCoreAngle (projectiveOriginalFlow y t₀ s)
      let x := fun s => k * coreProjectedFlowVariation y t₀ s w 1
      |x t| ≤ Real.exp (-k * (θ t - θ a) / 4) *
        (|x a| + 3 * k * projectiveOriginalFlow y t₀ a 1 * Q * (θ t - θ a)) := by
  let beta := projectiveOriginalFlow y t₀
  let θ := fun s => projectiveCoreAngle (beta s)
  let rate := fun s => coreOriginalClockRate (beta s)
  let xi := fun s => coreProjectedFlowVariation y t₀ s w
  let v := fun s => scaleCoreVariation k (xi s)
  let B := fun s => coreWeightedJacobian k (θ s) (toCoreAngleState (beta s))
  let d := fun s => B s 1 1
  let g := fun s => B s 1 0 * v s 0 + B s 1 2 * v s 2
  let x := fun s => k * xi s 1
  have hk0 : 0 < k := by linarith only [hk]
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ a ⟨le_rfl, hab⟩)
  have hrate (s : ℝ) (hs : s ∈ Icc a b) : 0 < rate s := (coreRegion_clock_regular hk (hcore s hs)).2.2
  have hV (s : ℝ) (hs : s ∈ Icc a b) : 0 < beta s 2 := lt_of_lt_of_le zero_lt_one (hcore s hs).2.1
  have hθ (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt θ (rate s) s :=
    hasDerivAt_coreAngle_scaled (hasDerivAt_projectiveOriginalFlow_time hD (hdom hs) (hA s hs)) (hV s hs)
  have hcoef (s : ℝ) (hs : s ∈ Icc a b) : d s ≤ -k / 4 ∧ |g s| ≤ 3 * k * beta s 1 * Q :=
    coreRegion_strong_forcing hk (hcore s hs) (hQ s hs)
  have hx (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt x (rate s * (d s * x s + g s)) s := by
    have hxi := hasDerivAt_coreProjectedFlowVariation hD (hdom hs) (hA s hs) (hV s hs)
      (ne_of_gt (coreRegion_clock_regular hk (hcore s hs)).2.1) w
    have H := (hasDerivAt_pi.mp hxi 1).const_mul k
    have he := congrArg (fun V : CoreAngleState => V 1)
      (coreWeightedJacobian_mulVec (ne_of_gt hk0) (θ s) (toCoreAngleState (beta s)) (xi s))
    change (B s).mulVec (v s) 1 = k * (coreAngleJacobian (θ s) (toCoreAngleState (beta s))).mulVec (xi s) 1 at he
    have hrow : (B s).mulVec (v s) 1 = d s * x s + g s := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      dsimp [d, g, v, x, scaleCoreVariation]
      ring
    convert! H using 1
    rw [← hrow, he]
    change rate s * (k * _) = k * (rate s * _)
    ring
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hu (s : ℝ) (hs : s ∈ Icc a b) :
      beta s 1 ≤ beta a 1 * Real.exp (-k * (θ s - θ a) / 4) := by
    exact (normalized_core_prefix_contraction hk (convex_Icc a b) hdom hc hA
      (show a ∈ Icc a b from ⟨le_rfl, hab⟩) hs hs.1
      (fun t ht => (coreRegion_radius_bounds hk (hcore t ht)).1)
      (fun t ht => (hcore t ht).2.1) (fun t ht => (coreRegion_wall_bounds (hcore t ht)).1)
      (fun t ht => (coreRegion_wall_bounds (hcore t ht)).2)).1
  have hg (s : ℝ) (hs : s ∈ Icc a b) :
      |g s| ≤ (3 * k * beta a 1 * Q) * Real.exp (-(k / 4) * (θ s - θ a)) := by
    calc
      _ ≤ 3 * k * beta s 1 * Q := (hcoef s hs).2
      _ ≤ 3 * k * (beta a 1 * Real.exp (-k * (θ s - θ a) / 4)) * Q := by gcongr; exact hu s hs
      _ = _ := by
        rw [show -k * (θ s - θ a) / 4 = -(k / 4) * (θ s - θ a) by ring]
        ring
  have H := abs_le_affine_exp_of_clock_damping hx hθ (fun s hs => (hrate s hs).le)
    (fun s hs => by convert! (hcoef s hs).1 using 1; ring) hg
  intro t ht
  convert! H t ht using 1
  congr 2
  ring
