-- Prove2me | solution 1 for BianchiIX.exists_terminal_single_correction_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:30:20.758192+00:00
-- url     : https://prove2.me/submissions/aac370d1-b575-48a4-87d2-28573302cbb8

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_entranceSinglePhaseError_differential
import Theorems.Thm_BianchiIX_exists_entranceSinglePhaseError_direction_bound
import Theorems.Thm_BianchiIX_exists_entranceSingleReciprocalError_direction_bounds
import Theorems.Thm_BianchiIX_exists_stableStrongProjectionError_bounds
import Theorems.Thm_BianchiIX_exists_terminalEntranceInput_derivative_uniform
import Theorems.Thm_BianchiIX_exists_terminalWallFactor_bounds_uniform
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_endpoint_uniform
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_variation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_hasFDerivAt_stableBoundaryProjection_in_band
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_integral_le_of_exp_decay
import Theorems.Thm_BianchiIX_norm_le_exp_of_signedRowSum
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_stable_global_region
import Theorems.Thm_BianchiIX_normalized_stable_limit
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_scaled_stable_boundary_drift
import Theorems.Thm_BianchiIX_stableRescaledDifferential_stable_decay
import Theorems.Thm_BianchiIX_stableRescaledJacobian_center_bounds
import Theorems.Thm_BianchiIX_terminalCyclicInput_radial_wall_bounds
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Arsinh
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open BianchiIX
open Filter
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

private theorem BianchiIX.stable_boundary_field (m u w : ℝ) :
    phaseVelocity m u 0 w = m * u ^ 2 - (m + 1) * u * w + w ^ 2 ∧
    strongVelocity m u 0 w = stableStrongRate m u w * u ∧
    activeVelocity m u 0 w = 0 ∧
    weakVelocity m u 0 w = stableWeakRate m u w * w := by
  unfold phaseVelocity strongVelocity activeVelocity weakVelocity coupling
    stableStrongRate stableWeakRate
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_band {m c : ℝ} (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    3 ≤ c + 1 ∧ 5 / 8 * (c + 1) ≤ m ∧ 0 ≤ m ∧ m ≤ c + 1 ∧
      0 ≤ m + 1 ∧ m + 1 ≤ 2 * (c + 1) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hm
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_rates {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) :
    stableStrongRate m u w / (c + 1) ≤ -(c + 1) / 8 ∧
      stableWeakRate m u w / (c + 1) ≤ -(1 / 4) := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hK0 : 0 < c + 1 := by linarith
  have hu2 : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hu)
  have huw : |u * w| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  constructor
  · apply (div_le_iff₀ hK0).mpr
    unfold stableStrongRate
    nlinarith [sq_nonneg w, sq_nonneg (c + 1 - 3)]
  · apply (div_le_iff₀ hK0).mpr
    unfold stableWeakRate
    nlinarith [(abs_le.mp huw).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_denom {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) :
    0 < projectiveDenom m u 0 w ∧ projectiveDenom m u 0 w ≤ 2 * (c + 1) ^ 2 := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have heq : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [heq]
  have hd : |u - w| ≤ 1 / 50 := (abs_sub _ _).trans (by linarith)
  have hd2 : (u - w) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hd)
  have hm2 := (sq_le_sq₀ hm0 (by linarith : 0 ≤ c + 1)).mpr hmK
  constructor
  · positivity
  · nlinarith [sq_nonneg (c + 1 - 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleStrongInvariant_defect {m u : ℝ} (hm : m ≠ 0) :
    singleStrongInvariant m u - 2 = ((m - 1) ^ 2 + u ^ 2) / m := by
  unfold singleStrongInvariant
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleStrongInvariant_gt_two {m u : ℝ} (hm : 0 < m) (hn : m ≠ 1 ∨ u ≠ 0) :
    2 < singleStrongInvariant m u := by
  have hnum : 0 < (m - 1) ^ 2 + u ^ 2 := by
    rcases hn with h | h
    · have H := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
      nlinarith only [H, sq_nonneg u]
    · have H := sq_pos_of_ne_zero h
      nlinarith only [H, sq_nonneg (m - 1)]
  have H := singleStrongInvariant_defect (u := u) hm.ne'
  linarith only [H, div_pos hnum hm]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleStrongRoot_relations {I : ℝ} (hI : 2 < I) :
    1 < singleStrongUpperRoot I ∧ 0 < singleStrongLowerRoot I ∧ singleStrongLowerRoot I < 1 ∧
      singleStrongLowerRoot I + singleStrongUpperRoot I = I ∧
      singleStrongLowerRoot I * singleStrongUpperRoot I = 1 := by
  have hD : 0 < I ^ 2 - 4 := by nlinarith
  have hS := Real.sqrt_nonneg (I ^ 2 - 4)
  have hsq := Real.sq_sqrt hD.le
  have hSI : Real.sqrt (I ^ 2 - 4) < I := by nlinarith
  have hSlo : I - 2 < Real.sqrt (I ^ 2 - 4) := by nlinarith
  dsimp [singleStrongLowerRoot, singleStrongUpperRoot]
  refine ⟨by linarith, by linarith, by linarith, by ring, ?_⟩
  nlinarith only [hsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleStrongUpperRoot_unique {I q : ℝ} (hI : 2 < I) (hq : 1 < q)
    (hpoly : q ^ 2 - I * q + 1 = 0) : q = singleStrongUpperRoot I := by
  obtain ⟨_, _, hl, hsum, hprod⟩ := singleStrongRoot_relations hI
  have hfactor : (q - singleStrongLowerRoot I) * (q - singleStrongUpperRoot I) = 0 := by
    nlinarith only [hpoly, hprod, congrArg (fun z : ℝ => z * q) hsum]
  rcases mul_eq_zero.mp hfactor with h | h
  · have H := sub_eq_zero.mp h
    linarith
  · exact sub_eq_zero.mp h

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_singleStrongInvariant (n : WithTop ℕ∞) {y : Fin 3 → ℝ} (hm : y 0 ≠ 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => singleStrongInvariant (z 0) (z 1)) y := by
  unfold singleStrongInvariant
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_singleStrongInvariant {m u : ℝ → ℝ} {a t : ℝ}
    (hm : HasDerivAt m (a * (m t * u t ^ 2)) t)
    (hu : HasDerivAt u (a * ((1 - m t ^ 2 + u t ^ 2) / 2 * u t)) t) (hn : m t ≠ 0) :
    HasDerivAt (fun s => singleStrongInvariant (m s) (u s)) 0 t := by
  apply ((((hm.pow 2).const_add 1).add (hu.pow 2)).div hm hn).congr_deriv
  dsimp
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

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

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_projectiveOriginalFlow_initial {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasFDerivAt (fun z => projectiveOriginalFlow z t₀ t) (projectiveFlowDifferential y t₀ t) y := by
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toProjectiveState 1 (ne_of_gt hA)).differentiableAt (by norm_num)).hasFDerivAt
  exact hto.comp y ((hasFDerivAt_normalizedMaxCurve_initial ht).comp y hfrom)

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
open Set MeasureTheory

private theorem BianchiIX.abs_le_exp_of_clock_damping {f d z z' : ℝ → ℝ} {a b c : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (z' t * (d t * f t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzpos : ∀ t ∈ Icc a b, 0 ≤ z' t)
    (hd : ∀ t ∈ Icc a b, d t ≤ -c) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| * Real.exp (-c * (z t - z a)) := by
  have H := abs_le_affine_exp_of_clock_damping (g := fun _ => 0) (B := 0)
    (by simpa only [add_zero] using hf) hz hzpos hd (by simp)
  simpa only [zero_mul, mul_zero, add_zero, mul_comm] using H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.scaled_stable_boundary_decay {Y : ℝ → ProjectiveState} {a z : ℝ → ℝ}
    {s t c : ℝ} (hc : 2 ≤ c)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hz : ∀ r ∈ Icc s t, HasDerivAt z ((c + 1) * a r) r)
    (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hv : ∀ r ∈ Icc s t, Y r 2 = 0)
    (hm : ∀ r ∈ Icc s t, |Y r 0 - c| ≤ 1 / 10)
    (hu : ∀ r ∈ Icc s t, |Y r 1| ≤ 1 / 100)
    (hw : ∀ r ∈ Icc s t, |Y r 3| ≤ 1 / 100) :
    ∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(c + 1) / 8 * (z r - z s)) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 / 4) * (z r - z s)) := by
  have hK : 0 < c + 1 := by linarith
  have hcoord (i : Fin 4) (r : ℝ) (hr : r ∈ Icc s t) := hasDerivAt_pi.mp (hY r hr) i
  have hU (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 1)
        (((c + 1) * a r) * (stableStrongRate (Y r 0) (Y r 1) (Y r 3) / (c + 1) * Y r 1)) r := by
    convert! hcoord 1 r hr using 1
    change _ = a r * strongVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    rw [hv r hr, (stable_boundary_field (Y r 0) (Y r 1) (Y r 3)).2.1]
    field_simp
  have hW (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 3)
        (((c + 1) * a r) * (stableWeakRate (Y r 0) (Y r 1) (Y r 3) / (c + 1) * Y r 3)) r := by
    convert! hcoord 3 r hr using 1
    change _ = a r * weakVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    rw [hv r hr, (stable_boundary_field (Y r 0) (Y r 1) (Y r 3)).2.2.2]
    field_simp
  have H := abs_le_exp_of_clock_damping hU hz (fun r hr => mul_nonneg hK.le (ha r hr))
    (fun r hr => by simpa only [neg_div] using (stable_boundary_rates hc (hm r hr) (hu r hr) (hw r hr)).1)
  have J := abs_le_exp_of_clock_damping hW hz (fun r hr => mul_nonneg hK.le (ha r hr))
    (fun r hr => (stable_boundary_rates hc (hm r hr) (hu r hr) (hw r hr)).2)
  intro r hr
  exact ⟨by simpa only [neg_div] using H r hr, J r hr⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.hasDerivAt_normalizedStableClock {x : NormalizedState} {t₀ s c t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (normalizedStableClock x t₀ s c)
      ((c + 1) * normalizedProjectiveRate x t₀ t) t :=
  ((hasStrictDerivAt_integralClock (convex_normalizedMaxDomain x t₀)
    (isOpen_normalizedMaxDomain x t₀) (continuousOn_normalizedProjectiveRate x t₀) hs ht).hasDerivAt).const_mul _

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.normalized_stable_prefix_estimates {x : NormalizedState} {t₀ s t c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r)
    (hy : ∀ r ∈ Icc s t, stableBoundaryRegion c (toProjectiveState (normalizedMaxCurve x t₀ r))) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y t 0 - Y s 0| ≤ 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) ∧
    (∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(c + 1) / 8 * normalizedStableClock x t₀ s c r) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 / 4) * normalizedStableClock x t₀ s c r)) ∧
    (∀ r ∈ Icc s t, |Y r 1| ≤ |Y s 1| ∧ |Y r 3| ≤ |Y s 3|) := by
  intro Y
  have hdom (r : ℝ) (hr : s ≤ r) : r ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt Y (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hx (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA r hr)) H.2.1
  have hz (r : ℝ) (hr : r ∈ Icc s t) :=
    hasDerivAt_normalizedStableClock (c := c) (hdom s le_rfl) (hdom r hr.1)
  have hac : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  have H := scaled_stable_boundary_decay hc hY hz (fun r hr => (hA r hr).le)
    (fun r hr => (hy r hr).2.2.1) (fun r hr => (hy r hr).1)
    (fun r hr => (hy r hr).2.1) (fun r hr => (hy r hr).2.2.2)
  have hzero : normalizedStableClock x t₀ s c s = 0 := by
    simp [normalizedStableClock, integralClock_initial]
  simp only [hzero, sub_zero] at H
  refine ⟨scaled_stable_boundary_drift hst hc hY hz hac (fun r hr => (hA r hr).le)
    (fun r hr => (hy r hr).2.2.1) (fun r hr => (hy r hr).1)
    (fun r hr => (hy r hr).2.1) (fun r hr => (hy r hr).2.2.2), H, ?_⟩
  intro r hr
  have hz0 : 0 ≤ normalizedStableClock x t₀ s c r := by
    apply mul_nonneg (by linarith : 0 ≤ c + 1)
    apply intervalIntegral.integral_nonneg hr.1
    intro q hq
    exact (hA q ⟨hq.1, hq.2.trans hr.2⟩).le
  constructor
  · exact (H r hr).1.trans (mul_le_of_le_one_right (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz0)))
  · exact (H r hr).2.trans (mul_le_of_le_one_right (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (by linarith)))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.normalizedStableClock_lower {x : NormalizedState} {t₀ s t c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate x t₀ r) :
    3 / (c + 1) * (t - s) ≤ normalizedStableClock x t₀ s c t := by
  have hK : 0 < c + 1 := by linarith
  have hcA : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono
      (fun r hr => normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hr.1))
  have H := intervalIntegral.integral_mono_on (μ := volume) hst (intervalIntegrable_const (c := 3 / (c + 1) ^ 2))
    (hcA.intervalIntegrable_of_Icc hst) hA
  rw [intervalIntegral.integral_const] at H
  have H' := mul_le_mul_of_nonneg_left H hK.le
  convert! H' using 1
  simp only [smul_eq_mul]
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryEntry_denom_pos (m u w : ℝ) :
    0 < projectiveStateDenom (stableBoundaryEntry m u w) := by
  change 0 < projectiveDenom m u 0 w
  have H : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [H]
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_initial (m u w : ℝ) :
    stableBoundaryOrbit m u w 0 = stableBoundaryEntry m u w := by
  unfold stableBoundaryOrbit
  rw [normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (stableBoundaryEntry_denom_pos m u w))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_global {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    ∀ t ≥ 0,
      3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 t ∧
      stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
      |stableBoundaryOrbit m u w t 0 - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) ∧
      |stableBoundaryOrbit m u w t 1| ≤ |u| ∧ |stableBoundaryOrbit m u w t 3| ≤ |w| := by
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_global_region hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  have H' := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  change ∀ t ≥ 0, _ ∧ stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
    |stableBoundaryOrbit m u w t 0 - stableBoundaryOrbit m u w 0 0| ≤
      8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) ∧
    |stableBoundaryOrbit m u w t 1| ≤ |stableBoundaryOrbit m u w 0 1| ∧
    |stableBoundaryOrbit m u w t 3| ≤ |stableBoundaryOrbit m u w 0 3| at H'
  simpa [hi, stableBoundaryEntry] using H'

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_exists {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (fun t => stableBoundaryOrbit m u w t 0) atTop (𝓝 (stableBoundaryProjection m u w)) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 1) atTop (𝓝 0) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 3) atTop (𝓝 0) ∧
    (∀ t ≥ 0, |stableBoundaryProjection m u w - stableBoundaryOrbit m u w t 0| ≤
      8 * (|stableBoundaryOrbit m u w t 1| + |stableBoundaryOrbit m u w t 3|) ^ 2 / (c + 1)) ∧
    |stableBoundaryProjection m u w - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_limit hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  obtain ⟨P, hP, hU, hW, htail⟩ := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  have heq : stableBoundaryProjection m u w = P := hP.limUnder_eq
  rw [heq]
  refine ⟨hP, hU, hW, htail, ?_⟩
  have H0 := htail 0 le_rfl
  change |P - stableBoundaryOrbit m u w 0 0| ≤
    8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) at H0
  simpa [hi, stableBoundaryEntry] using H0

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_band {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    |stableBoundaryProjection m u w - c| ≤ 1 / 10 := by
  apply le_of_tendsto (((stableBoundaryProjection_exists hc hm hu hw).1.sub_const c).abs)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (stableBoundaryOrbit_global hc hm hu hw t ht).2.1.1

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_apply (y : StableState) : stableInclusion y = ![y 0, y 1, 0, y 2] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRestriction_apply (y : ProjectiveState) : stableRestriction y = ![y 0, y 1, y 3] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_entry (y : StableState) :
    stableInclusion y = stableBoundaryEntry (y 0) (y 1) (y 2) := stableInclusion_apply y

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRestriction_inclusion (y : StableState) : stableRestriction (stableInclusion y) = y := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_restriction {y : ProjectiveState} (hy : y 2 = 0) :
    stableInclusion (stableRestriction y) = y := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hy.symm
  · rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_pos (y : StableState) : 0 < stableBoundaryDenom y := by
  unfold stableBoundaryDenom
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_eq (y : StableState) :
    projectiveStateDenom (stableInclusion y) = stableBoundaryDenom y := by
  change projectiveDenom (y 0) (y 1) 0 (y 2) = _
  unfold projectiveDenom curvature stableBoundaryDenom
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryField_inclusion (y : StableState) :
    projectiveField (stableInclusion y) = stableInclusion (stableBoundaryField y) := by
  obtain ⟨hM, hU, hV, hW⟩ := stable_boundary_field (y 0) (y 1) (y 2)
  ext i
  fin_cases i
  · exact hM
  · exact hU
  · exact hV
  · exact hW

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_inclusion (y : StableState) :
    projectiveOriginalField (stableInclusion y) = stableInclusion (stableOriginalField y) := by
  rw [projectiveOriginalField, stableBoundaryDenom_eq, stableBoundaryField_inclusion,
    stableOriginalField, map_smul]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_restriction {y : ProjectiveState} (hy : y 2 = 0) :
    stableRestriction (projectiveOriginalField y) = stableOriginalField (stableRestriction y) := by
  rw [← stableInclusion_restriction hy, stableOriginalField_inclusion, stableRestriction_inclusion,
    stableRestriction_inclusion]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableBoundaryField (n : WithTop ℕ∞) : ContDiff ℝ n stableBoundaryField := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [stableBoundaryField, stableStrongRate, stableWeakRate] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableBoundaryDenom (n : WithTop ℕ∞) : ContDiff ℝ n stableBoundaryDenom := by
  unfold stableBoundaryDenom
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableOriginalField (n : WithTop ℕ∞) : ContDiff ℝ n stableOriginalField := by
  apply (contDiff_const.div (contDiff_stableBoundaryDenom n)
    (fun y => ne_of_gt (stableBoundaryDenom_pos y))).smul (contDiff_stableBoundaryField n)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_active_zero (m u w : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    stableBoundaryOrbit m u w t 2 = 0 := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hzero : wallValue 1 x = 0 := by
    simp [x, wallValue, fromProjectiveState, stableBoundaryEntry]
  have H := (normalizedMaxCurve_wall_sign hx ht 1).1.mpr hzero
  change normalizedMaxCurve x 0 t 3 = 0 at H
  change Real.sqrt 3 * normalizedMaxCurve x 0 t 3 / (1 + normalizedMaxCurve x 0 t 0) = 0
  rw [H, mul_zero, zero_div]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_eq (y : StableState) (t : ℝ) :
    stableOriginalFlow y t = stableRestriction (stableBoundaryOrbit (y 0) (y 1) (y 2) t) := by
  simp only [stableOriginalFlow, stableInclusion_entry, projectiveOriginalFlow, stableBoundaryOrbit]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableProjectiveFlow_active_zero (y : StableState) {t : ℝ} (ht : 0 ≤ t) :
    projectiveOriginalFlow (stableInclusion y) 0 t 2 = 0 := by
  simpa only [stableInclusion_entry, projectiveOriginalFlow, stableBoundaryOrbit] using
    stableBoundaryOrbit_active_zero (y 0) (y 1) (y 2) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableProjectiveFlow_rate_pos {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    0 < normalizedProjectiveRate (fromProjectiveState (stableInclusion y)) 0 t := by
  have hK : 0 < c + 1 := by linarith
  rw [stableInclusion_entry]
  exact lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2)
    (stableBoundaryOrbit_global hc hm hu hw t ht).1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_initial (y : StableState) : stableOriginalFlow y 0 = y := by
  rw [stableOriginalFlow_eq, stableBoundaryOrbit_initial, ← stableInclusion_entry]
  exact stableRestriction_inclusion y

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableFlowDifferential_initial (y : StableState) :
    stableFlowDifferential y 0 = ContinuousLinearMap.id ℝ StableState := by
  rw [stableFlowDifferential, projectiveFlowDifferential_initial
    (by rw [stableBoundaryDenom_eq]; exact stableBoundaryDenom_pos y), ContinuousLinearMap.id_comp]
  ext v i
  exact congrFun (stableRestriction_inclusion v) i

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableOriginalFlow {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    HasDerivAt (stableOriginalFlow y) (stableOriginalField (stableOriginalFlow y t)) t := by
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have H := stableRestriction.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_projectiveOriginalFlow_time hD hdom hA)
  rw [stableOriginalField_restriction (stableProjectiveFlow_active_zero y ht)] at H
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableFlowDifferential_apply {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) (v : StableState) :
    HasDerivAt (fun s => stableFlowDifferential y s v)
      (fderiv ℝ stableOriginalField (stableOriginalFlow y t) (stableFlowDifferential y t v)) t := by
  let alpha := projectiveOriginalFlow (stableInclusion y) 0
  let V := fun s => projectiveFlowDifferential (stableInclusion y) 0 s (stableInclusion v)
  let b := fun z : StableState => projectiveOriginalFlow (stableInclusion z) 0 t
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have hb := (hasFDerivAt_projectiveOriginalFlow_initial hD hdom hA).comp y stableInclusion.hasFDerivAt
  have halpha := hasDerivAt_projectiveOriginalFlow_time hD hdom hA
  have hV := hasDerivAt_projectiveFlowDifferential_apply hD hdom hA (stableInclusion v)
  have hDout : 0 < projectiveStateDenom (alpha t) := by
    have hcon := (normalizedMaxCurve_constraint hdom).trans (fromProjectiveState_constraint (ne_of_gt hD))
    exact toProjectiveState_denom_pos hA hcon
  have heq : (fun z => fderiv ℝ stableRestriction (b z) (projectiveOriginalField (b z))) =ᶠ[𝓝 y]
      (fun z => stableOriginalField (stableRestriction (b z))) := by
    apply Eventually.of_forall
    intro z
    simp only [stableRestriction.fderiv]
    exact stableOriginalField_restriction (stableProjectiveFlow_active_zero z ht)
  have H := hasDerivAt_coordinate_variation stableRestriction.contDiff.contDiffAt
    ((contDiffAt_projectiveOriginalField 1 hDout.ne').differentiableAt (by norm_num))
    ((contDiff_stableOriginalField 1).differentiable (by norm_num) (stableRestriction (alpha t)))
    halpha hV hb rfl rfl heq
  simpa only [stableRestriction.fderiv, stableFlowDifferential, stableOriginalFlow, alpha,
    ContinuousLinearMap.comp_apply] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryField {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableBoundaryField (gamma s))
      ((stableBoundaryJacobian (gamma t)).mulVec v) t := by
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply (((hm.mul (hu.pow 2)).sub (((hm.add_const 1).mul hu).mul hw)).add
      (hw.pow 2)).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply ((((((hasDerivAt_const t (1 : ℝ)).sub (hm.pow 2)).sub
      (hw.pow 2)).add (hu.pow 2)).div_const 2).mul hu).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply ((((hm.add_const 1).add (hu.mul hw)).sub (hu.pow 2)).neg.mul hw).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryDenom {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableBoundaryDenom (gamma s))
      (dotProduct (stableDenomGradient (gamma t)) v) t := by
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply (((hm.pow 2).const_add 3).add ((hu.sub hw).pow 2)).congr_deriv
  simp [stableDenomGradient, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableOriginalField {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableOriginalField (gamma s))
      ((stableOriginalJacobian (gamma t)).mulVec v) t := by
  have hd := hasDerivAt_stableBoundaryDenom h
  have hf := hasDerivAt_stableBoundaryField h
  apply (((hasDerivAt_const t (6 : ℝ)).div hd
    (stableBoundaryDenom_pos (gamma t)).ne').smul hf).congr_deriv
  ext i
  simp [stableOriginalJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_fderiv (y v : StableState) :
    fderiv ℝ stableOriginalField y v = (stableOriginalJacobian y).mulVec v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf := ((contDiff_stableOriginalField 1).differentiable (by norm_num) y).hasFDerivAt
  have hzero : y + (0 : ℝ) • v = y := by simp
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_stableOriginalField hl)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableFlow_variational_equation {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) (v : StableState) :
    HasDerivAt (fun s => stableFlowDifferential y s v)
      ((stableOriginalJacobian (stableOriginalFlow y t)).mulVec (stableFlowDifferential y t v)) t := by
  simpa only [stableOriginalField_fderiv] using
    hasDerivAt_stableFlowDifferential_apply hc hm hu hw ht v

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledDifferential_initial (K : ℝ) (y : StableState) :
    stableRescaledDifferential K y 0 = ContinuousLinearMap.id ℝ StableState := by
  simp only [stableRescaledDifferential, mul_zero, stableFlowDifferential_initial]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledFlow_variational_equation {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    HasDerivAt (fun r => stableRescaledDifferential K y r v)
      (K • (stableOriginalJacobian (stableRescaledFlow K y s)).mulVec
        (stableRescaledDifferential K y s v)) s := by
  exact (stableFlow_variational_equation hc hm hu hw (mul_nonneg hK.le hs) v).scomp s
    (by simpa using (hasDerivAt_id s).const_mul K)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_limit {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Tendsto (stableOriginalFlow y) atTop (𝓝 ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) := by
  have H := stableBoundaryProjection_exists hc hm hu hw
  apply tendsto_pi_nhds.mpr
  intro i
  simp_rw [stableOriginalFlow_eq, stableRestriction_apply]
  fin_cases i
  · exact H.1
  · exact H.2.1
  · exact H.2.2.1

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_rate_denom_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableStrongRate (y 0) (y 1) (y 2)| ≤ stableBoundaryDenom y ∧
      |stableWeakRate (y 0) (y 1) (y 2)| ≤ stableBoundaryDenom y := by
  have hK : 0 < c + 1 := by linarith
  have hr := stable_boundary_rates hc hm hu hw
  have hs := (div_le_iff₀ hK).mp hr.1
  have hw' := (div_le_iff₀ hK).mp hr.2
  have hs0 : stableStrongRate (y 0) (y 1) (y 2) ≤ 0 := by nlinarith
  have hw0 : stableWeakRate (y 0) (y 1) (y 2) ≤ 0 := by nlinarith
  rw [abs_of_nonpos hs0, abs_of_nonpos hw0]
  have huw : |y 1 * y 2| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  obtain ⟨huwl, huwu⟩ := abs_le.mp huw
  unfold stableStrongRate stableWeakRate stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
  · nlinarith [sq_nonneg (y 0 - 1 / 2), sq_nonneg (y 1), sq_nonneg (y 2)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_field_div_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableBoundaryField y 1 / stableBoundaryDenom y| ≤ |y 1| ∧
      |stableBoundaryField y 2 / stableBoundaryDenom y| ≤ |y 2| := by
  have H := stableBoundary_rate_denom_bounds hc hm hu hw
  have hD := stableBoundaryDenom_pos y
  constructor
  · rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    change |stableStrongRate (y 0) (y 1) (y 2) * y 1| ≤ _
    rw [abs_mul, mul_comm _ (stableBoundaryDenom y)]
    exact mul_le_mul_of_nonneg_right H.1 (abs_nonneg _)
  · rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    change |stableWeakRate (y 0) (y 1) (y 2) * y 2| ≤ _
    rw [abs_mul, mul_comm _ (stableBoundaryDenom y)]
    exact mul_le_mul_of_nonneg_right H.2 (abs_nonneg _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_polynomial_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    stableBoundaryJacobian y 1 1 + |stableBoundaryJacobian y 1 2| +
        4 * (|y 1| + |y 2|) ^ 2 ≤ -(c + 1) ^ 2 / 16 ∧
    stableBoundaryJacobian y 2 2 + |stableBoundaryJacobian y 2 1| +
        4 * (|y 1| + |y 2|) ^ 2 ≤ -(c + 1) / 8 := by
  have hK : 0 < c + 1 := by linarith
  have hr := stable_boundary_rates hc hm hu hw
  have hs := (div_le_iff₀ hK).mp hr.1
  have hw' := (div_le_iff₀ hK).mp hr.2
  have hb : (|y 1| + |y 2|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hu2 : y 1 ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by norm_num; exact hu)
  have huw : |y 1 * y 2| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  have hcross : |(2 * y 1 - y 2) * y 2| ≤ 3 / 10000 := by
    rw [abs_mul]
    have H : |2 * y 1 - y 2| ≤ 3 / 100 := by
      have H' := abs_sub (2 * y 1) (y 2)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H'
      linarith
    nlinarith [mul_le_mul H hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 100)]
  constructor
  · change (1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2 + |-y 1 * y 2| + _ ≤ _
    rw [neg_mul, abs_neg]
    unfold stableStrongRate at hs
    nlinarith [sq_nonneg (c + 1 - 3)]
  · change -(y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2) + |(2 * y 1 - y 2) * y 2| + _ ≤ _
    unfold stableWeakRate at hw'
    nlinarith [(abs_le.mp huw).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_factor (y : StableState) (i j : Fin 3) :
    stableOriginalJacobian y i j = 6 / stableBoundaryDenom y *
      (stableBoundaryJacobian y i j - stableBoundaryField y i / stableBoundaryDenom y *
        stableDenomGradient y j) := by
  unfold stableOriginalJacobian
  field_simp [(stableBoundaryDenom_pos y).ne']

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_rational_row {a d f g h D b : ℝ}
    (hD : 0 < D) (hb : 0 ≤ b) (hf : |f / D| ≤ b) (hg : |g| ≤ 2 * b) (hh : |h| ≤ 2 * b) :
    6 / D * (a - f / D * g) + |6 / D * (d - f / D * h)| ≤
      6 / D * (a + |d| + 4 * b ^ 2) := by
  have h1 : |f / D * g| ≤ 2 * b ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hf hg (abs_nonneg _) hb]
  have h2 : |f / D * h| ≤ 2 * b ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hf hh (abs_nonneg _) hb]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 6 / D)]
  have H : a - f / D * g + |d - f / D * h| ≤ a + |d| + 4 * b ^ 2 := by
    have H' := abs_sub d (f / D * h)
    nlinarith [(abs_le.mp h1).1]
  have H' := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ 6 / D)
  nlinarith only [H']

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_stable_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    stableOriginalJacobian y 1 1 + |stableOriginalJacobian y 1 2| ≤
        6 / stableBoundaryDenom y * (-(c + 1) ^ 2 / 16) ∧
    stableOriginalJacobian y 2 2 + |stableOriginalJacobian y 2 1| ≤
        6 / stableBoundaryDenom y * (-(c + 1) / 8) := by
  have hD := stableBoundaryDenom_pos y
  have hf := stableBoundary_field_div_bounds hc hm hu hw
  have hr := stableBoundary_polynomial_rows hc hm hu hw
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hg1 : |stableDenomGradient y 1| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 1 - y 2)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
  have hg2 : |stableDenomGradient y 2| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := abs_sub (y 2) (y 1)
    linarith
  simp_rw [stableOriginalJacobian_factor]
  constructor
  · exact (stable_rational_row hD hb (hf.1.trans (by linarith [abs_nonneg (y 2)])) hg1 hg2).trans
      (mul_le_mul_of_nonneg_left hr.1 (by positivity))
  · exact (stable_rational_row hD hb (hf.2.trans (by linarith [abs_nonneg (y 1)])) hg2 hg1).trans
      (mul_le_mul_of_nonneg_left hr.2 (by positivity))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_stable_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    (c + 1) * (stableOriginalJacobian y 1 1 + |stableOriginalJacobian y 1 2|) ≤
        -3 * (c + 1) / 16 ∧
    (c + 1) * (stableOriginalJacobian y 2 2 + |stableOriginalJacobian y 2 1|) ≤
        -(3 / 8) := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hDup : stableBoundaryDenom y ≤ 2 * (c + 1) ^ 2 := by
    have H := (stable_boundary_denom hc hm hu hw).2
    change projectiveStateDenom (stableBoundaryEntry (y 0) (y 1) (y 2)) ≤ _ at H
    rwa [← stableInclusion_entry, stableBoundaryDenom_eq] at H
  have H := stableOriginalJacobian_stable_rows hc hm hu hw
  constructor
  · apply (mul_le_mul_of_nonneg_left H.1 hK.le).trans
    have heq : (c + 1) * (6 / stableBoundaryDenom y * (-(c + 1) ^ 2 / 16)) =
        (-3 * (c + 1) ^ 3 / 8) / stableBoundaryDenom y := by ring
    rw [heq]
    apply (div_le_iff₀ hD).mpr
    nlinarith [mul_le_mul_of_nonneg_left hDup hK.le]
  · apply (mul_le_mul_of_nonneg_left H.2 hK.le).trans
    have heq : (c + 1) * (6 / stableBoundaryDenom y * (-(c + 1) / 8)) =
        (-3 * (c + 1) ^ 2 / 4) / stableBoundaryDenom y := by ring
    rw [heq]
    apply (div_le_iff₀ hD).mpr
    linarith

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_single_strong_region {m c u t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) (ht : 0 ≤ t) :
    1 < stableOriginalFlow ![m, u, 0] t 0 ∧ stableOriginalFlow ![m, u, 0] t 2 = 0 := by
  have H := stableBoundaryOrbit_global hc hm hu (by norm_num : |(0 : ℝ)| ≤ 1 / 200) t ht
  have hM : |stableOriginalFlow ![m, u, 0] t 0 - c| ≤ 1 / 10 := by
    simpa [stableOriginalFlow_eq, stableRestriction_apply] using H.2.1.1
  have hW : |stableOriginalFlow ![m, u, 0] t 2| ≤ 0 := by
    simpa [stableOriginalFlow_eq, stableRestriction_apply] using H.2.2.2.2
  exact ⟨by linarith [(abs_le.mp hM).1], abs_eq_zero.mp (le_antisymm hW (abs_nonneg _))⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableSingleStrongInvariant {m c u t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) (ht : 0 ≤ t) :
    HasDerivAt (fun s => singleStrongInvariant (stableOriginalFlow ![m, u, 0] s 0)
      (stableOriginalFlow ![m, u, 0] s 1)) 0 t := by
  have H := hasDerivAt_stableOriginalFlow (y := ![m, u, 0]) hc hm hu
    (by change |(0 : ℝ)| ≤ 1 / 200; norm_num) ht
  obtain ⟨hM, hW⟩ := stableOriginalFlow_single_strong_region hc hm hu ht
  apply hasDerivAt_singleStrongInvariant (a := 6 / stableBoundaryDenom (stableOriginalFlow ![m, u, 0] t))
  · simpa [stableOriginalField, stableBoundaryField, hW] using hasDerivAt_pi.mp H 0
  · simpa [stableOriginalField, stableBoundaryField, stableStrongRate, hW] using hasDerivAt_pi.mp H 1
  · linarith

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableSingleStrongInvariant_constant {m c u t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) (ht : 0 ≤ t) :
    singleStrongInvariant (stableOriginalFlow ![m, u, 0] t 0) (stableOriginalFlow ![m, u, 0] t 1) =
      singleStrongInvariant m u := by
  have H := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_stableSingleStrongInvariant hc hm hu hs).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) (by simp : (0 : ℝ) ∈ Ici 0) ht
  simpa [sub_eq_zero, stableOriginalFlow_initial] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_single_strong_invariant {m c u : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) :
    singleStrongInvariant (stableBoundaryProjection m u 0) 0 = singleStrongInvariant m u := by
  have hP : 1 < stableBoundaryProjection m u 0 := by
    have H := (abs_le.mp (stableBoundaryProjection_band (w := 0) hc hm hu (by norm_num))).1
    linarith
  have hlim := stableOriginalFlow_limit (y := ![m, u, 0]) hc hm hu
    (by change |(0 : ℝ)| ≤ 1 / 200; norm_num)
  have hreg := contDiffAt_singleStrongInvariant 0 (y := ![stableBoundaryProjection m u 0, 0, 0]) (by simpa using (ne_of_gt (show 0 < stableBoundaryProjection m u 0 by linarith)))
  have H := hreg.continuousAt.tendsto.comp hlim
  have heq : (fun t => singleStrongInvariant (stableOriginalFlow ![m, u, 0] t 0)
      (stableOriginalFlow ![m, u, 0] t 1)) =ᶠ[atTop] (fun _ => singleStrongInvariant m u) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact stableSingleStrongInvariant_constant hc hm hu ht
  exact tendsto_nhds_unique H ((tendsto_congr' heq).mpr tendsto_const_nhds)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_strong {m c u : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) :
    stableBoundaryProjection m u 0 = singleStrongUpperRoot (singleStrongInvariant m u) := by
  have hm1 : 1 < m := by linarith [(abs_le.mp hm).1]
  have hI := singleStrongInvariant_gt_two (u := u) (by linarith : 0 < m) (Or.inl (ne_of_gt hm1))
  have hP : 1 < stableBoundaryProjection m u 0 := by
    have H := (abs_le.mp (stableBoundaryProjection_band (w := 0) hc hm hu (by norm_num))).1
    linarith
  apply singleStrongUpperRoot_unique hI hP
  have H := stableBoundaryProjection_single_strong_invariant hc hm hu
  have hP0 : stableBoundaryProjection m u 0 ≠ 0 := by linarith
  unfold singleStrongInvariant at H
  simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at H
  have H' := (div_eq_iff hP0).mp H
  dsimp [singleStrongInvariant]
  nlinarith only [H']

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledFlow_band {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 0 - c| ≤ 1 / 10 ∧
    |stableRescaledFlow (c + 1) y s 1| ≤ 1 / 100 ∧
    |stableRescaledFlow (c + 1) y s 2| ≤ 1 / 100 := by
  have ht : 0 ≤ (c + 1) * s := mul_nonneg (by linarith) hs
  have H := (stableBoundaryOrbit_global hc hm hu hw ((c + 1) * s) ht).2.1
  simp only [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply]
  exact ⟨H.1, H.2.1, H.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_lower {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    (c + 1) ^ 2 ≤ 3 * stableBoundaryDenom y ∧ c + 1 ≤ stableBoundaryDenom y := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  unfold stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 1 - y 2)]
  · nlinarith [sq_nonneg (y 1 - y 2), sq_nonneg (c + 1 - 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_scaled_entry_bound {y : StableState} {c B : ℝ} {i j : Fin 3}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (hB : 0 ≤ B)
    (hentry : |stableBoundaryJacobian y i j -
      stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤ 3 * (c + 1) * B) :
    |(c + 1) * stableOriginalJacobian y i j| ≤ 64 * B := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hscale : 6 * (c + 1) ^ 2 / stableBoundaryDenom y ≤ 18 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith [(stableBoundaryDenom_lower hc hm).1]
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos hK, abs_mul,
    abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y)]
  calc
    _ ≤ (c + 1) * (6 / stableBoundaryDenom y * (3 * (c + 1) * B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hentry (by positivity)) hK.le
    _ = (6 * (c + 1) ^ 2 / stableBoundaryDenom y) * (3 * B) := by ring
    _ ≤ 18 * (3 * B) := mul_le_mul_of_nonneg_right hscale (by positivity)
    _ ≤ 64 * B := by linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_center_column {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 0| ≤ 64 * |y 1| ∧
    |(c + 1) * stableOriginalJacobian y 2 0| ≤ 64 * |y 2| := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have H := stableBoundary_field_div_bounds hc hm hu hw
  have hg : |stableDenomGradient y 0| ≤ 2 * (c + 1) := by
    change |2 * y 0| ≤ _
    rw [abs_of_nonneg (by positivity)]
    linarith
  constructor
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 1| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.1 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 1 0| ≤ (c + 1) * |y 1| := by
      change |-y 0 * y 1| ≤ _
      rw [abs_mul, abs_neg, abs_of_nonneg hm0]
      exact mul_le_mul_of_nonneg_right hmK (abs_nonneg _)
    have H' := abs_sub (stableBoundaryJacobian y 1 0)
      (stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 2| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.2 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 2 0| ≤ (c + 1) * |y 2| := by
      change |-y 2| ≤ _
      rw [abs_neg]
      nlinarith [abs_nonneg (y 2)]
    have H' := abs_sub (stableBoundaryJacobian y 2 0)
      (stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledFlow_wall_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 1| ≤ |y 1| * Real.exp (-3 * (c + 1) / 8 * s) ∧
    |stableRescaledFlow (c + 1) y s 2| ≤ |y 2| * Real.exp (-(3 / 4) * s) := by
  let x := fromProjectiveState (stableBoundaryEntry (y 0) (y 1) (y 2))
  let Y := stableBoundaryOrbit (y 0) (y 1) (y 2)
  let z := normalizedStableClock x 0 0 c
  have hK : 0 < c + 1 := by linarith
  have ht : 0 ≤ (c + 1) * s := mul_nonneg hK.le hs
  have hx : stateConstraint x = 1 :=
    fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos (y 0) (y 1) (y 2)))
  have hg := stableBoundaryOrbit_global hc hm hu hw
  have hdec := (normalized_stable_prefix_estimates hx hc (le_refl 0) ht
    (fun r hr => lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) (hg r hr.1).1)
    (fun r hr => (hg r hr.1).2.1)).2.1 ((c + 1) * s) ⟨ht, le_rfl⟩
  have hz : 3 * s ≤ z ((c + 1) * s) := by
    have H := normalizedStableClock_lower hx hc (le_refl 0) ht (fun r hr => (hg r hr.1).1)
    convert! H using 1
    simp only [sub_zero]
    field_simp
  have hU : |Y ((c + 1) * s) 1| ≤ |y 1| * Real.exp (-(c + 1) / 8 * z ((c + 1) * s)) := by
    have H := hdec.1
    change |Y ((c + 1) * s) 1| ≤ |Y 0 1| * Real.exp (-(c + 1) / 8 * z ((c + 1) * s)) at H
    simpa [Y, stableBoundaryOrbit_initial, stableBoundaryEntry] using H
  have hW : |Y ((c + 1) * s) 3| ≤ |y 2| * Real.exp (-(1 / 4) * z ((c + 1) * s)) := by
    have H := hdec.2
    change |Y ((c + 1) * s) 3| ≤ |Y 0 3| * Real.exp (-(1 / 4) * z ((c + 1) * s)) at H
    simpa [Y, stableBoundaryOrbit_initial, stableBoundaryEntry] using H
  simp only [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply]
  constructor
  · exact hU.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hz hK.le])) (abs_nonneg _))
  · exact hW.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledFlow_amplitude_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 1| + |stableRescaledFlow (c + 1) y s 2| ≤
      (|y 1| + |y 2|) * Real.exp (-s / 2) := by
  have H := stableRescaledFlow_wall_decay hc hm hu hw hs
  have hU : Real.exp (-3 * (c + 1) / 8 * s) ≤ Real.exp (-s / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hW : Real.exp (-(3 / 4) * s) ≤ Real.exp (-s / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have H' := add_le_add (H.1.trans (mul_le_mul_of_nonneg_left hU (abs_nonneg _)))
    (H.2.trans (mul_le_mul_of_nonneg_left hW (abs_nonneg _)))
  nlinarith only [H']

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledJacobian_signedRowSum {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i : Fin 3) :
    signedRowSum ((c + 1) • stableOriginalJacobian y) i ≤ 256 * (|y 1| + |y 2|) := by
  have hK : 0 < c + 1 := by linarith
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have hb2 : (|y 1| + |y 2|) ^ 2 ≤ |y 1| + |y 2| := by nlinarith
  have H := stableRescaledJacobian_center_bounds hc hm hu hw
  have C := stableRescaledJacobian_center_column hc hm hu hw
  have S := stableRescaledJacobian_stable_rows hc hm hu hw
  simp only [abs_mul, abs_of_pos hK] at H C
  have hfin : Finset.univ = ({0, 1, 2} : Finset (Fin 3)) := by decide
  fin_cases i
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    have hd := mul_le_mul_of_nonneg_left (le_abs_self (stableOriginalJacobian y 0 0)) hK.le
    nlinarith only [H.1, H.2.1, H.2.2, hd, hb2, hb]
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    nlinarith only [S.1, C.1, hc, abs_nonneg (y 1), abs_nonneg (y 2)]
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    nlinarith only [S.2, C.2, abs_nonneg (y 1), abs_nonneg (y 2)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledDifferential_bound {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    ‖stableRescaledDifferential (c + 1) y s v‖ ≤
      Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ := by
  let b := |y 1| + |y 2|
  let J := fun r => stableRescaledDifferential (c + 1) y r v
  let A := fun r => (c + 1) • stableOriginalJacobian (stableRescaledFlow (c + 1) y r)
  let z := fun r => 512 * b * (1 - Real.exp (-r / 2))
  have hK : 0 < c + 1 := by linarith
  have hJ (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt J ((A r).mulVec (J r)) r := by
    simpa only [A, Matrix.smul_mulVec] using
      stableRescaledFlow_variational_equation hK hc hm hu hw hr.1 v
  have hz (r : ℝ) : HasDerivAt z (256 * b * Real.exp (-r / 2)) r := by
    convert! ((hasDerivAt_const r (1 : ℝ)).sub (((hasDerivAt_id r).neg.div_const 2).exp)).const_mul
      (512 * b) using 1
    dsimp
    ring
  have hrow (r : ℝ) (hr : r ∈ Ico 0 s) (i : Fin 3) :
      signedRowSum (A r) i ≤ 256 * b * Real.exp (-r / 2) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hr.1
    have H := stableRescaledJacobian_signedRowSum hc hm' hu' hw' i
    have H' := mul_le_mul_of_nonneg_left (stableRescaledFlow_amplitude_decay hc hm hu hw hr.1)
      (by norm_num : (0 : ℝ) ≤ 256)
    exact H.trans (by nlinarith only [H'])
  have H := norm_le_exp_of_signedRowSum (HasDerivAt.continuousOn hJ)
    (fun r hr => hJ r (Ico_subset_Icc_self hr))
    (HasDerivAt.continuousOn (fun r _ => hz r)) (fun r _ => hz r) hrow s ⟨hs, le_rfl⟩
  have hzero : J 0 = v := by simp only [J, stableRescaledDifferential_initial, ContinuousLinearMap.id_apply]
  have hz0 : z 0 = 0 := by simp [z]
  rw [hzero, hz0, sub_zero] at H
  have hzb : z s ≤ 512 * b := by
    have hb : 0 ≤ b := by dsimp [b]; positivity
    dsimp [z]
    nlinarith [Real.exp_pos (-s / 2)]
  have H' := H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzb) (norm_nonneg v))
  simpa only [mul_comm] using H'

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableVariationCenterBudget_nonneg (y v : StableState) : 0 ≤ stableVariationCenterBudget y v := by
  unfold stableVariationCenterBudget
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableRescaledJacobian_center_apply {y v : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * (stableOriginalJacobian y).mulVec v 0| ≤
      64 * (|y 1| + |y 2|) ^ 2 * |v 0| + 128 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ := by
  have H := stableRescaledJacobian_center_bounds hc hm hu hw
  have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := by
    simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 0
  have hv2 : |v 2| ≤ ‖![v 1, v 2]‖ := by
    simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 1
  have heq : (c + 1) * (stableOriginalJacobian y).mulVec v 0 =
      ((c + 1) * stableOriginalJacobian y 0 0) * v 0 +
      (((c + 1) * stableOriginalJacobian y 0 1) * v 1 +
       ((c + 1) * stableOriginalJacobian y 0 2) * v 2) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  rw [heq]
  have htri := (abs_add_le (((c + 1) * stableOriginalJacobian y 0 0) * v 0)
    ((((c + 1) * stableOriginalJacobian y 0 1) * v 1) +
      (((c + 1) * stableOriginalJacobian y 0 2) * v 2))).trans
        (add_le_add (le_refl _) (abs_add_le _ _))
  simp only [abs_mul] at htri
  have h0 := mul_le_mul_of_nonneg_right H.1 (abs_nonneg (v 0))
  have h1 := mul_le_mul H.2.1 hv1 (abs_nonneg _) (by positivity)
  have h2 := mul_le_mul H.2.2 hv2 (abs_nonneg _) (by positivity)
  simp only [abs_mul] at h0 h1 h2
  nlinarith only [htri, h0, h1, h2]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableRescaledDifferential_center_rate {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    |(c + 1) * (stableOriginalJacobian (stableRescaledFlow (c + 1) y s)).mulVec
      (stableRescaledDifferential (c + 1) y s v) 0| ≤
      stableVariationCenterBudget y v * Real.exp (-s / 2) := by
  let b := |y 1| + |y 2|
  let Y := stableRescaledFlow (c + 1) y s
  let J := stableRescaledDifferential (c + 1) y s v
  let B := |Y 1| + |Y 2|
  let M := Real.exp (512 * b) * ‖v‖
  let N := ‖![v 1, v 2]‖
  let e := Real.exp (-s / 2)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hN : 0 ≤ N := norm_nonneg _
  have he : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hs
  have H := stableRescaledJacobian_center_apply (v := J) hc hm' hu' hw'
  have hBe : B ≤ b * e := stableRescaledFlow_amplitude_decay hc hm hu hw hs
  have hBb : B ≤ b := hBe.trans (mul_le_of_le_one_right hb he1)
  have hB2 : B ^ 2 ≤ b ^ 2 * e := by
    nlinarith only [mul_le_mul hBb hBe hB hb]
  have hJ0 : |J 0| ≤ M := by
    have H' : |J 0| ≤ ‖J‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm J 0
    exact H'.trans (stableRescaledDifferential_bound hc hm hu hw hs v)
  have hZ : ‖![J 1, J 2]‖ ≤ N + 256 * b * M := by
    have H' : ‖![J 1, J 2]‖ ≤ (N + 256 * b * M) * Real.exp (-s / 4) := by
      convert! stableRescaledDifferential_stable_decay hc hm hu hw hs v using 1
      dsimp [M, b, N]
      ring
    exact H'.trans (mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by linarith)))
  have h1 := mul_le_mul hB2 hJ0 (abs_nonneg _) (by positivity : 0 ≤ b ^ 2 * e)
  have h2 := mul_le_mul hBe hZ (norm_nonneg _) (mul_nonneg hb he)
  change |(c + 1) * (stableOriginalJacobian Y).mulVec J 0| ≤ 64 * B ^ 2 * |J 0| +
    128 * B * ‖![J 1, J 2]‖ at H
  have hout : |(c + 1) * (stableOriginalJacobian Y).mulVec J 0| ≤
      (128 * b * N + 33000 * b ^ 2 * M) * e := by
    nlinarith only [H, h1, h2, mul_nonneg (mul_nonneg (sq_nonneg b) hM) he]
  convert! hout using 1
  dsimp [stableVariationCenterBudget, b, N, M, e]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableRescaledDifferential_center_tail {y : StableState} {c a t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ha : 0 ≤ a) (hat : a ≤ t) (v : StableState) :
    |stableRescaledDifferential (c + 1) y t v 0 - stableRescaledDifferential (c + 1) y a v 0| ≤
      2 * stableVariationCenterBudget y v * Real.exp (-a / 2) := by
  let C := stableVariationCenterBudget y v
  have hC : 0 ≤ C := stableVariationCenterBudget_nonneg y v
  have hK : 0 < c + 1 := by linarith
  have hf (r : ℝ) (hr : r ∈ Icc a t) :=
    hasDerivAt_pi.mp (stableRescaledFlow_variational_equation hK hc hm hu hw (ha.trans hr.1) v) 0
  have hcont : Continuous (fun r : ℝ => C * Real.exp (-r / 2)) := by fun_prop
  have H := abs_sub_le_integral_bound hat hf hcont.continuousOn
    (fun r hr => stableRescaledDifferential_center_rate hc hm hu hw (ha.trans hr.1) v)
  have HI := integral_le_of_exp_decay (f := fun r : ℝ => C * Real.exp (-r / 2))
    (B := C * Real.exp (-a / 2)) (c := (1 / 2 : ℝ)) hat (by norm_num)
    (by positivity) hcont.continuousOn (fun r _ => ?_)
  · exact H.trans (by convert! HI using 1; ring)
  · have heq : C * Real.exp (-r / 2) =
        (C * Real.exp (-a / 2)) * Real.exp (-(1 / 2) * (r - a)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring
    exact heq.le

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableRescaledDifferential_center_drift {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    |stableRescaledDifferential (c + 1) y s v 0 - v 0| ≤ 2 * stableVariationCenterBudget y v := by
  simpa only [stableRescaledDifferential_initial, ContinuousLinearMap.id_apply, neg_zero, zero_div,
    Real.exp_zero, mul_one] using stableRescaledDifferential_center_tail hc hm hu hw (le_refl 0) hs v

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterTailCoefficient_nonneg (y : StableState) : 0 ≤ stableCenterTailCoefficient y := by
  unfold stableCenterTailCoefficient
  positivity

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableVariationCenterBudget_le_norm (y v : StableState) :
    stableVariationCenterBudget y v ≤ stableCenterTailCoefficient y * ‖v‖ := by
  have hv : ‖![v 1, v 2]‖ ≤ ‖v‖ := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · exact norm_le_pi_norm v 2
  have H := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 128 * (|y 1| + |y 2|))
  unfold stableVariationCenterBudget stableCenterTailCoefficient
  nlinarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterDifferential_tail {y : StableState} {c a t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ha : 0 ≤ a) (hat : a ≤ t) :
    ‖stableCenterDifferential c y t - stableCenterDifferential c y a‖ ≤
      2 * stableCenterTailCoefficient y * Real.exp (-a / 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [stableCenterTailCoefficient_nonneg y])
  intro v
  change |stableRescaledDifferential (c + 1) y t v 0 - stableRescaledDifferential (c + 1) y a v 0| ≤ _
  have H := stableRescaledDifferential_center_tail hc hm hu hw ha hat v
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stableVariationCenterBudget_le_norm y v) (by norm_num : (0 : ℝ) ≤ 2))
    (Real.exp_pos (-a / 2)).le
  exact H.trans (by nlinarith only [H'])

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterTailCoefficient_decay (y : StableState) :
    Tendsto (fun t : ℝ => 2 * stableCenterTailCoefficient y * Real.exp (-t / 2)) atTop (𝓝 0) := by
  have H := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) tendsto_id)).const_mul
      (2 * stableCenterTailCoefficient y)
  convert! H using 1
  · ext t
    simp only [Function.comp_def, id_eq]
    congr 2
    ring
  · simp

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterDifferential_tendsto {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Tendsto (stableCenterDifferential c y) atTop (𝓝 (stableCenterDifferentialLimit c y)) := by
  have hC : CauchySeq (stableCenterDifferential c y) := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.mp ((stableCenterTailCoefficient_decay y).eventually (gt_mem_nhds hε))
    refine ⟨max R 0, fun t ht => ?_⟩
    rw [dist_eq_norm]
    exact (stableCenterDifferential_tail hc hm hu hw (le_max_right _ _) ht).trans_lt
      (hR _ (le_max_left _ _))
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hC
  have heq : stableCenterDifferentialLimit c y = L := hL.limUnder_eq
  rwa [heq]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_fderiv_eq {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y =
      stableCenterDifferentialLimit c y :=
  (hasFDerivAt_stableBoundaryProjection_in_band hc hm hu hw).fderiv

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_fderiv_drift {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (v : StableState) :
    |fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v - v 0| ≤
      2 * stableVariationCenterBudget y v := by
  rw [stableBoundaryProjection_fderiv_eq hc hm hu hw]
  have heval : ContinuousAt (fun L : StableState →L[ℝ] ℝ => L v) (stableCenterDifferentialLimit c y) :=
    continuousAt_id.clm_apply continuousAt_const
  have H := heval.tendsto.comp (stableCenterDifferential_tendsto hc hm.le hu.le hw.le)
  apply le_of_tendsto ((H.sub_const (v 0)).abs)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact stableRescaledDifferential_center_drift hc hm.le hu.le hw.le hs v

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryProjection_two {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y :=
  contDiffAt_stableBoundaryProjection_two_in_band hm (by simp) hu hw

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePhase_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceStablePhase y v =
      fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
        (stableRestriction y) (stableRestriction v) := by
  have H := ((contDiffAt_stableBoundaryProjection_two (y := stableRestriction y) hm hu hw).differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) H.fderiv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStableRadius_sq (y : ProjectiveState) :
    entranceStableRadius y ^ 2 = (entranceStablePhase y - 1) ^ 2 + y 2 ^ 2 :=
  coreRadius_sq _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePhase_small_wall_bounds {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 10000) (hw : |y 3| ≤ 1 / 10000) :
    |entranceStablePhase y - y 0| ≤ 1 / 100 ∧
      |entranceStablePartial y 0 - 1| ≤ 1 / 2 := by
  have hu' : |y 1| < 1 / 200 := by linarith
  have hw' : |y 3| < 1 / 200 := by linarith
  let b := |y 1| + |y 3|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 / 5000 := by dsimp [b]; linarith
  have hb2 : b ^ 2 ≤ (1 / 5000 : ℝ) ^ 2 := pow_le_pow_left₀ hb hb1 2
  have hval : |entranceStablePhase y - y 0| ≤ 8 * b ^ 2 / (y 0 + 1) :=
    (stableBoundaryProjection_exists hm (by simp) hu'.le hw'.le).2.2.2.2
  have hvec : stableRestriction (Pi.single (0 : Fin 4) (1 : ℝ)) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  have hd := stableBoundaryProjection_fderiv_drift (y := stableRestriction y) hm
    (by simp [stableRestriction]) hu' hw' (Pi.single 0 1)
  have hd' : |entranceStablePartial y 0 - 1| ≤ 66000 * b ^ 2 * Real.exp (512 * b) := by
    rw [entranceStablePartial, entranceStablePhase_fderiv hm hu' hw', hvec]
    have hz : (![0, 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
    simp [stableVariationCenterBudget, stableRestriction_apply, Pi.norm_single, hz] at hd
    rw [stableRestriction_apply]
    convert! hd using 1
    ring
  have he : Real.exp (512 * b) ≤ 2 :=
    (Real.exp_bound_div_one_sub_of_interval (by positivity) (by linarith)).trans
      ((div_le_iff₀ (by linarith : 0 < 1 - 512 * b)).mpr (by linarith))
  constructor
  · apply hval.trans
    apply (div_le_iff₀ (by linarith : 0 < y 0 + 1)).mpr
    nlinarith only [hb2, hm]
  · have H := mul_le_mul hb2 he (Real.exp_pos _).le (by positivity : (0 : ℝ) ≤ (1 / 5000) ^ 2)
    nlinarith only [hd', H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableStrongProjectionError_eventuallyEq_single {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) :
    stableStrongProjectionError =ᶠ[𝓝 y] (fun z : StableState =>
      stableBoundaryProjection (z 0) (z 1) (z 2) -
        singleStrongUpperRoot (singleStrongInvariant (z 0) (z 1))) := by
  have HMc : ContinuousAt (fun z : StableState => |z 0 - y 0|) y :=
    (((continuous_apply 0).sub continuous_const).abs).continuousAt
  have HUc : ContinuousAt (fun z : StableState => |z 1|) y := (continuous_apply 1).abs.continuousAt
  have HM : ∀ᶠ z : StableState in 𝓝 y, |z 0 - y 0| < 1 / 40 :=
    HMc.eventually
      (isOpen_Iio.mem_nhds (by simp : |y 0 - y 0| < (1 / 40 : ℝ)))
  have HU : ∀ᶠ z : StableState in 𝓝 y, |z 1| < 1 / 200 :=
    HUc.eventually (isOpen_Iio.mem_nhds hu)
  filter_upwards [HM, HU] with z hz huZ
  rw [stableStrongProjectionError, stableBoundaryProjection_strong hm hz.le huZ.le]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceSinglePhaseError_decomposition {y : ProjectiveState}
    (hP : 1 < entranceStablePhase y) :
    entranceSinglePhaseError y = stableStrongProjectionError (stableRestriction y) +
      (y 2) ^ 2 / (entranceStableRadius y + entranceStablePhase y - 1) := by
  have HR : 0 ≤ entranceStableRadius y := Real.sqrt_nonneg _
  have HD : 0 < entranceStableRadius y + entranceStablePhase y - 1 := by linarith only [HR, hP]
  have HS := entranceStableRadius_sq y
  change entranceStableRadius y - (stableBoundaryProjection (y 0) (y 1) 0 - 1) =
    entranceStablePhase y - stableBoundaryProjection (y 0) (y 1) 0 + _
  have Hroot : entranceStableRadius y - (entranceStablePhase y - 1) =
      (y 2) ^ 2 / (entranceStableRadius y + entranceStablePhase y - 1) := by
    apply (eq_div_iff HD.ne').mpr
    nlinarith only [HS]
  linarith only [Hroot]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePhase_large_lower {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 10000) (hw : |y 3| ≤ 1 / 10000) :
    (y 0 + 1) / 4 ≤ entranceStablePhase y - 1 ∧ 1 < entranceStablePhase y := by
  have HP := (entranceStablePhase_small_wall_bounds hm hu hw).1
  have HM := (abs_le.mp HP).1
  constructor <;> linarith only [HM, hm]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_entranceSinglePhaseError_bounds :
    ∃ C > (0 : ℝ), ∀ y : ProjectiveState,
      2 ≤ y 0 → |y 1| ≤ 1 / 10000 → |y 3| ≤ 1 / 10000 →
      let b := |y 1| + |y 3|
      |entranceSinglePhaseError y| ≤ C * (|y 3| * b + (y 2) ^ 2) / (y 0 + 1) := by
  obtain ⟨C, hC, HC⟩ := exists_stableStrongProjectionError_bounds
  refine ⟨C + 4, by positivity, ?_⟩
  intro y hm hu hw b
  have hu' : |y 1| < 1 / 200 := by linarith only [hu]
  have hw' : |y 3| < 1 / 200 := by linarith only [hw]
  have HP := entranceStablePhase_large_lower hm hu hw
  have hL : 0 < y 0 + 1 := by linarith only [hm]
  have HR : 0 ≤ entranceStableRadius y := Real.sqrt_nonneg _
  have HD : (y 0 + 1) / 4 ≤ entranceStableRadius y + entranceStablePhase y - 1 := by
    linarith only [HP.1, HR]
  have HDpos : 0 < entranceStableRadius y + entranceStablePhase y - 1 := lt_of_lt_of_le (by positivity) HD
  have HE := (HC (stableRestriction y) hm hu' hw').1
  change |stableStrongProjectionError (stableRestriction y)| ≤ C * |y 3| * b / (y 0 + 1) at HE
  rw [entranceSinglePhaseError_decomposition HP.2]
  calc
    _ ≤ |stableStrongProjectionError (stableRestriction y)| +
        |(y 2) ^ 2 / (entranceStableRadius y + entranceStablePhase y - 1)| := abs_add_le _ _
    _ = |stableStrongProjectionError (stableRestriction y)| +
        (y 2) ^ 2 / (entranceStableRadius y + entranceStablePhase y - 1) := by
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) HDpos.le)]
    _ ≤ C * |y 3| * b / (y 0 + 1) + (y 2) ^ 2 / ((y 0 + 1) / 4) :=
      add_le_add HE (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) HD)
    _ = (C * |y 3| * b + 4 * (y 2) ^ 2) / (y 0 + 1) := by field_simp
    _ ≤ (C + 4) * (|y 3| * b + (y 2) ^ 2) / (y 0 + 1) := by
      apply (div_le_div_iff_of_pos_right hL).mpr
      have hb : 0 ≤ b := by dsimp only [b]; positivity
      nlinarith only [mul_nonneg hC.le (sq_nonneg (y 2)), mul_nonneg (abs_nonneg (y 3)) hb]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_entranceSinglePhaseError_scaled_bounds :
    ∃ C > (0 : ℝ), ∀ (α : ℝ) (y : ProjectiveState), 0 < α → 1 / α ≤ y 0 + 1 →
      2 ≤ y 0 → |y 1| ≤ 1 / 10000 → |y 3| ≤ 1 / 10000 →
      |entranceSinglePhaseError y| ≤ C * α * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceSinglePhaseError_bounds
  refine ⟨C, hC, ?_⟩
  intro α y hα hscale hm hu hw
  have HL : 0 < y 0 + 1 := by linarith only [hm]
  have Hinv : 1 / (y 0 + 1) ≤ α := (div_le_iff₀ HL).mpr
    (by have H := (div_le_iff₀ hα).mp hscale; nlinarith only [H])
  refine (HC y hm hu hw).trans ?_
  calc
    _ = (C * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2)) * (1 / (y 0 + 1)) := by ring
    _ ≤ (C * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2)) * α :=
      mul_le_mul_of_nonneg_left Hinv (by positivity)
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceSingleReciprocalError_eventuallyEq_single {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) :
    entranceSingleReciprocalError =ᶠ[𝓝 y] (fun z : ProjectiveState =>
      2 / entranceStableRadius z - singleStrongPhase (z 0) (z 1)) := by
  have HE := (stableStrongProjectionError_eventuallyEq_single (y := stableRestriction y) hm hu).comp_tendsto
    stableRestriction.continuous.continuousAt.tendsto
  filter_upwards [HE] with z hz
  have HQ : stableBoundaryProjection (z 0) (z 1) 0 = singleStrongUpperRoot (singleStrongInvariant (z 0) (z 1)) := by
    change stableBoundaryProjection (z 0) (z 1) (z 3) - stableBoundaryProjection (z 0) (z 1) 0 =
      stableBoundaryProjection (z 0) (z 1) (z 3) - singleStrongUpperRoot (singleStrongInvariant (z 0) (z 1)) at hz
    linarith only [hz]
  simp only [entranceSingleReciprocalError, entranceSingleRadius, singleStrongPhase, HQ]

end
end


/-- The two stable corrections are estimated after composition with the actual finite tail. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := terminalCyclicInput h Y
      let E := |z 3| * (|z 1| + |z 3|) + (z 2) ^ 2
      let e := entranceSinglePhaseError ∘ terminalCyclicInput h
      let q := terminalSingleReciprocalError h
      coreTailValid h Y ∧ ContDiffAt ℝ 2 e Y ∧ ContDiffAt ℝ 2 q Y ∧
        |e Y| ≤ C * α * E ∧ |fderiv ℝ e Y (Pi.single 0 1)| ≤ C * E ∧
        |q Y| ≤ C * α ^ 3 * E ∧ |fderiv ℝ q Y (Pi.single 0 1)| ≤ C * α ^ 2 * E := by
  obtain ⟨A, hA, HA⟩ := exists_entranceSinglePhaseError_direction_bound
  obtain ⟨B, hB, HB⟩ := exists_entranceSinglePhaseError_scaled_bounds
  obtain ⟨Q, hQ, HQ⟩ := exists_entranceSingleReciprocalError_direction_bounds
  have hη1000 : 0 < η₀ ∧ η₀ ≤ 1 / 1000 := ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩
  have hη100 : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩
  obtain ⟨D, hD, εd, hεd, HD⟩ := exists_terminalEntranceInput_derivative_uniform hη1000 hJ
  obtain ⟨M, hM, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη100 hJ
  obtain ⟨K, hK, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform hη100 hJ
  let L := D + M
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hD, hM]
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL
  let C := (A + B + Q + 1) * (L + 1)
  have hcoeff : A ≤ A + B + Q + 1 ∧ B ≤ A + B + Q + 1 ∧ Q ≤ A + B + Q + 1 := by
    constructor <;> [skip; constructor] <;> linarith only [hA, hB, hQ]
  have hAC : A * L ≤ C := mul_le_mul hcoeff.1 (by linarith) hL0 (by positivity)
  have hBC : B ≤ C := by
    have H := mul_le_mul hcoeff.2.1 (by linarith only [hL0] : (1 : ℝ) ≤ L + 1) (by norm_num) (by positivity)
    simpa only [mul_one] using H
  have hQC : Q ≤ C := by
    have H := mul_le_mul hcoeff.2.2 (by linarith only [hL0] : (1 : ℝ) ≤ L + 1) (by norm_num) (by positivity)
    simpa only [mul_one] using H
  have hQLC : Q * L ≤ C := mul_le_mul hcoeff.2.2 (by linarith) hL0 (by positivity)
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let ε := min εd (min εm (min εg (1 / (20000 * K))))
  refine ⟨C, ?_, ε, lt_min hεd (lt_min hεm (lt_min hεg (by positivity))), ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (by linarith only [hA, hB, hQ]) (by linarith only [hL0])
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h z E e q
  have hα0 := hα.1
  have hη0 := hη₀.1.trans_le hηlo
  have hs (a : ℝ) (ha : ε ≤ a) : b ≤ a * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right ha (pow_nonneg hα.1.le _))
  have hsd := hs εd (min_le_left _ _)
  have hsm := hs εm ((min_le_right _ _).trans (min_le_left _ _))
  have hsg := hs εg ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨HV, Hreg, Hinput, Hnorm, _, _⟩ := HD η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsd hsum
  obtain ⟨_, _, _, _, Hlog, HBfac⟩ := HM η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsm hsum
  obtain ⟨_, _, HH, Hm, _, Hu, Hw, _, _, _⟩ := HG η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsg hsum
  change 19 / (10 * α) < z 0 - 1 ∧ z 0 - 1 < 21 / (10 * α) at Hm
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at Hu
  change |z 2| ≤ 2 * (K * b) / α ^ 2 ∧ |z 3| ≤ 2 * (K * b) / α ^ 2 at Hw
  have Hlow : 1 / α ≤ 19 / (10 * α) := by
    apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.1]
  have hscale : 1 / α ≤ z 0 + 1 := by linarith only [Hlow, Hm.1]
  have hone : 1 ≤ 1 / α := (le_div_iff₀ hα.1).mpr (by simpa using hα.2)
  have hm : 2 ≤ z 0 := by linarith only [hone, Hlow, Hm.1]
  have hu : |z 1| ≤ 1 / 10000 := by
    have hz1 : 0 ≤ z 1 := (by positivity : 0 ≤ η / 2 * α ^ (J - 2)).trans Hu.1
    rw [abs_of_nonneg hz1]
    have HP := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J - 2)) (by positivity : 0 ≤ 2 * η)
    nlinarith only [Hu.2, HP, hηhi]
  have Hbudget : 2 * (K * b) ≤ α ^ 2 / 10000 := by
    have Hε : ε ≤ 1 / (20000 * K) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have HE := (le_div_iff₀ (by positivity : 0 < 20000 * K)).mp Hε
    have HP := pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)
    have H1 := mul_le_mul_of_nonneg_left hsmall hK0.le
    have H2 := mul_le_mul_of_nonneg_right HE (pow_nonneg hα.1.le (2 * J))
    nlinarith only [H1, H2, HP]
  have hw : |z 3| ≤ 1 / 10000 := Hw.2.trans ((div_le_iff₀ (sq_pos_of_pos hα.1)).mpr (by linarith only [Hbudget]))
  have hH : 0 < projectiveCycleDenom (coreTailState h Y) :=
    (by positivity : 0 < 399 / 100 * α ^ 2).trans HH.1
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have hDL : D ≤ L := by dsimp only [L]; linarith only [hM]
  have hML : M ≤ L := by dsimp only [L]; linarith only [hD]
  let d := fderiv ℝ (terminalCyclicInput h) Y (Pi.single 0 1)
  have hdnorm : ‖d‖ ≤ L / α ^ 2 := by
    have H := (fderiv ℝ (terminalCyclicInput h) Y).le_opNorm (Pi.single 0 1)
    simp only [Pi.norm_single, norm_one, mul_one] at H
    exact H.trans (Hnorm.trans (div_le_div_of_nonneg_right hDL (sq_nonneg α)))
  have hdwall : ∀ i : Fin 4, i ≠ 0 → |d i| ≤ L * |z i| / α :=
    terminalCyclicInput_radial_wall_bounds hR HV (mul_pos hη0 (pow_pos hα.1 J)) hH Hreg Hinput
      (Hlog.trans (div_le_div_of_nonneg_right hML hα.1.le))
      (fun i => (HBfac i).2.2.2.2.2.trans (div_le_div_of_nonneg_right hML hα.1.le))
  have He := HA α L z d hα.1 hL0 hscale hm hu hw hdnorm hdwall
  have He0 := HB α z hα.1 hscale hm hu hw
  obtain ⟨Hqreg, Hq0, HqD⟩ := HQ α L z d hα.1 hL0 hscale hm hu hw hdnorm hdwall
  have Hereg := (entranceSinglePhaseError_differential hm hu hw).1
  have Hnear : (entranceSingleReciprocalError ∘ terminalCyclicInput h) =ᶠ[𝓝 Y] q :=
    (entranceSingleReciprocalError_eventuallyEq_single hm (by linarith only [hu])).comp_tendsto
      Hreg.continuousAt.tendsto
  have Hqvalue : entranceSingleReciprocalError z = q Y := Hnear.self_of_nhds
  rw [Hqvalue] at Hq0
  have HEder : fderiv ℝ e Y (Pi.single 0 1) = fderiv ℝ entranceSinglePhaseError z d := by
    rw [fderiv_comp Y (Hereg.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
    rfl
  have HQder : fderiv ℝ q Y (Pi.single 0 1) = fderiv ℝ entranceSingleReciprocalError z d := by
    have HH : fderiv ℝ (entranceSingleReciprocalError ∘ terminalCyclicInput h) Y = fderiv ℝ q Y := Hnear.fderiv_eq
    rw [← HH]
    rw [fderiv_comp Y (Hqreg.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
    rfl
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨HV, Hereg.comp Y Hreg, (Hqreg.comp Y Hreg).congr_of_eventuallyEq Hnear.symm,
    He0.trans ?_, ?_, Hq0.trans ?_, ?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_right hBC (by positivity : 0 ≤ α * E)]
  · rw [HEder]
    exact He.trans (mul_le_mul_of_nonneg_right hAC hE)
  · nlinarith only [mul_le_mul_of_nonneg_right hQC (by positivity : 0 ≤ α ^ 3 * E)]
  · rw [HQder]
    nlinarith only [HqD, mul_le_mul_of_nonneg_right hQLC (by positivity : 0 ≤ α ^ 2 * E)]
