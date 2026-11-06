-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_initial_variation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:48:37.750214+00:00
-- url     : https://prove2.me/submissions/236d0705-dc2a-46a3-b8d3-41c28b1da338

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_ShearTransportData
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_exists_restartSectionMixedFlow_derivative
import Theorems.Thm_BianchiIX_exists_restartSectionWeakWall_derivative
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_cutoff_budget (C C₀ q : ℝ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, (0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
      C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 := by
  have HI : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun ρ : ℝ => ρ * Real.log ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HB : Tendsto (fun ρ : ℝ => 2 * C₀ * ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using HI.const_mul (2 * C₀)
  have HT : Tendsto (fun ρ : ℝ => C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) := by
    convert! HL.const_mul (-C * C₀ * q) using 1
    · ext ρ
      rw [one_div, Real.log_inv]
      ring
    · simp
  filter_upwards [show ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ from self_mem_nhdsWithin,
    HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    HB.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    HT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with ρ hρ hρ1 hb ht
  exact ⟨⟨hρ, hρ1.le⟩, hb.le, ht.le⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_negative_branch_root {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    -x 0 = Real.sqrt (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) := by
  have hr : 1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4) = x 0 ^ 2 := by
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hp]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_restartRadicand (k : WithTop ℕ∞) : ContDiff ℝ k restartRadicand := by
  unfold restartRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactRoot {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactRoot x :=
  (contDiff_restartRadicand k).contDiffAt.sqrt hx.ne'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactField {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactField x := by
  have hr := contDiffAt_restartCompactRoot hx k
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp [restartCompactField, restartCompactWeakRate, shearMinus, curvature] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_restartCompactField_zero : HasFDerivAt (𝕜 := ℝ) restartCompactField 0 0 := by
  have hp (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (0 : RestartState)
  have hQ : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => curvature (x 0) (x 2) (x 3)) 0 0 := by
    have H := (((hp 0).pow 2).add ((hp 2).pow 2) |>.add ((hp 3).pow 2)).sub
      ((((hp 0).mul (hp 2)).add ((hp 2).mul (hp 3)) |>.add ((hp 3).mul (hp 0))).const_mul 2)
    convert! H using 1
    simp
  have hR : HasFDerivAt (𝕜 := ℝ) restartRadicand 0 0 := by
    convert! (((hp 1).pow 2).const_sub 1).sub hQ using 1
    simp
  have hr : HasFDerivAt (𝕜 := ℝ) restartCompactRoot 0 0 := by
    convert! hR.sqrt (by norm_num [restartRadicand, curvature] : restartRadicand 0 ≠ 0) using 1
    simp
  have hH : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => -(x 2) ^ 2 + (x 3) ^ 2 + x 0 * x 2 - x 0 * x 3) 0 0 := by
    convert! ((((hp 2).pow 2).neg.add ((hp 3).pow 2)).add ((hp 0).mul (hp 2))).sub
      ((hp 0).mul (hp 3)) using 1
    simp
  have hg (ε : ℝ) := ((hQ.sub_const 1).add hr).add ((hp 1).const_mul (ε * Real.sqrt 3))
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert! (hQ.sub_const 1).sub (hr.const_mul 2) using 1
    simp
  · convert! (hQ.mul (hp 1)).add (hH.const_mul (Real.sqrt 3)) using 1
    simp [curvature]
  · convert! (hp 2).mul (hg 1) using 1
    simp [curvature, restartCompactRoot, restartRadicand]
  · convert! (hp 3).mul (hg (-1)) using 1
    simp [curvature, restartCompactRoot, restartRadicand]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartCompactField_fderiv_zero : fderiv ℝ restartCompactField 0 = 0 :=
  hasFDerivAt_restartCompactField_zero.fderiv

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompact_box_bounds {x : RestartState} (hx : ‖x‖ ≤ 1 / 16) :
    |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 ∧
      246 / 256 ≤ restartRadicand x ∧ restartRadicand x ≤ 265 / 256 ∧
      15 / 16 ≤ restartCompactRoot x ∧ restartCompactRoot x ≤ 17 / 16 ∧
      -4 < restartCompactField x 0 ∧ restartCompactField x 0 < -2 := by
  have hc (i : Fin 4) : |x i| ≤ 1 / 16 := (norm_le_pi_norm x i).trans hx
  have hs (i : Fin 4) : (x i) ^ 2 ≤ 1 / 256 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hc i)
    nlinarith only [hl, hu]
  have hm (i j : Fin 4) : |x i * x j| ≤ 1 / 256 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16) := mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQ : |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 := by
    obtain ⟨h02l, h02u⟩ := abs_le.mp (hm 0 2)
    obtain ⟨h23l, h23u⟩ := abs_le.mp (hm 2 3)
    obtain ⟨h30l, h30u⟩ := abs_le.mp (hm 3 0)
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h02u, h23u, h30u]
    · nlinarith only [hs 0, hs 2, hs 3, h02l, h23l, h30l]
  have hRl : 246 / 256 ≤ restartRadicand x := by
    dsimp only [restartRadicand]
    linarith only [hs 1, (abs_le.mp hQ).2]
  have hRu : restartRadicand x ≤ 265 / 256 := by
    dsimp only [restartRadicand]
    linarith only [sq_nonneg (x 1), (abs_le.mp hQ).1]
  have hr0 : 0 ≤ restartCompactRoot x := Real.sqrt_nonneg _
  have hr2 : restartCompactRoot x ^ 2 = restartRadicand x := Real.sq_sqrt (by linarith only [hRl])
  have hrl : 15 / 16 ≤ restartCompactRoot x := by nlinarith only [hr0, hr2, hRl]
  have hru : restartCompactRoot x ≤ 17 / 16 := by nlinarith only [hr0, hr2, hRu]
  refine ⟨hQ, hRl, hRu, hrl, hru, ?_, ?_⟩
  · change -4 < curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x
    linarith only [(abs_le.mp hQ).1, hru]
  · change curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x < -2
    linarith only [(abs_le.mp hQ).2, hrl]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartCompact_derivative_bounds :
    ∃ C ≥ (1 : ℝ), ∀ x : RestartState, ‖x‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartCompactField x‖ ≤ C * ‖x‖ ∧
        ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖ ≤ C := by
  let S := Metric.closedBall (0 : RestartState) (1 / 16)
  have hreg (x : RestartState) (hx : x ∈ S) : ContDiffAt ℝ 3 restartCompactField x := by
    have H := (restartCompact_box_bounds (by simpa [S] using hx)).2.1
    exact contDiffAt_restartCompactField (by linarith only [H]) 3
  have hq : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖) S := by
    intro x hx
    exact (((hreg x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : RestartState) (1 / 16)).exists_bound_of_continuousOn hq
  let C := max B 1
  have hbound (x : RestartState) (hx : x ∈ S) :
      ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖ ≤ C := by
    exact (le_abs_self _).trans ((hB x hx).trans (le_max_left B 1))
  have hdiff (x : RestartState) (hx : x ∈ S) : DifferentiableAt ℝ (fderiv ℝ restartCompactField) x :=
    ((hreg x hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hxS : x ∈ S := by simpa [S] using hx
  have hzS : (0 : RestartState) ∈ S := by simp [S]
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall (0 : RestartState) (1 / 16)) hzS hxS
  exact ⟨by simpa only [restartCompactField_fderiv_zero, sub_zero] using H, hbound x hxS⟩

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
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

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
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartCenterProjection_section (h : ℝ) (Z : RestartCenterState) :
    restartCenterProjection (restartSectionChart h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactCenterProjection_norm_le (x : RestartState) :
    ‖restartCompactCenterProjection x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm x 1
  · exact norm_le_pi_norm x 2
  · exact norm_le_pi_norm x 3

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysicalCoordinates_norm_le {x : NormalizedState} {R : ℝ} (hR : 0 ≤ R)
    (hn : |x 2| ≤ R) (hZ : ‖restartCenterProjection x‖ ≤ R) :
    ‖restartPhysicalCoordinates x‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hn
  · exact (norm_le_pi_norm (restartCenterProjection x) 0).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 1).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 2).trans hZ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactField_physical {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartCompactField (restartPhysicalCoordinates x) 0 = rateOne (x 0) (x 1) ∧
      restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x)) =
        restartCenterProjection (normalizedField x) := by
  have hroot := restart_negative_branch_root hc hp
  have hq : curvature (x 2) (x 3) (x 4) = 1 - shearSq (x 0) (x 1) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  constructor
  · change curvature (x 2) (x 3) (x 4) - 1 - 2 * Real.sqrt
      (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) = _
    rw [← hroot, hq]
    dsimp only [rateOne]
    ring
  · ext i
    fin_cases i
    · rfl
    · change x 3 * (curvature (x 2) (x 3) (x 4) - 1 + Real.sqrt
        (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) + 1 * Real.sqrt 3 * x 1) =
        rateTwo (x 0) (x 1) * x 3
      rw [← hroot, hq]
      dsimp only [rateTwo]
      ring
    · change x 4 * (curvature (x 2) (x 3) (x 4) - 1 + Real.sqrt
        (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) + (-1) * Real.sqrt 3 * x 1) =
        rateThree (x 0) (x 1) * x 4
      rw [← hroot, hq]
      dsimp only [rateThree]
      ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysical_shear_bound {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0)
    (hx : ‖restartPhysicalCoordinates x‖ ≤ 1 / 16) : x 0 ≤ -(15 / 16) := by
  have H := (restartCompact_box_bounds hx).2.2.2.1
  have heq : restartCompactRoot (restartPhysicalCoordinates x) = -x 0 :=
    (restart_negative_branch_root hc hp).symm
  rw [heq] at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCenterField_bound {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    {x : NormalizedState} (hc : stateConstraint x = 1) (hp : x 0 < 0)
    (hn : 0 ≤ x 2 ∧ x 2 ≤ 1 / 16) (hZ : ‖restartCenterProjection x‖ ≤ 1 / 16) :
    ‖restartCenterProjection (normalizedField x)‖ ≤
      C * (x 2 + ‖restartCenterProjection x‖) * ‖restartCenterProjection x‖ := by
  let r := ‖restartCenterProjection x‖
  let R := max (x 2) r
  let w : RestartState := ![x 2, 0, 0, 0]
  let S := Metric.closedBall (0 : RestartState) R
  have hR : 0 ≤ R := hn.1.trans (le_max_left _ _)
  have hRsmall : R ≤ 1 / 16 := max_le hn.2 hZ
  have hRsum : R ≤ x 2 + r := max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left hn.1)
  have hxS : restartPhysicalCoordinates x ∈ S := by
    simpa [S] using restartPhysicalCoordinates_norm_le hR
      (by simpa only [abs_of_nonneg hn.1] using le_max_left (x 2) r) (le_max_right (x 2) r)
  have hwS : w ∈ S := by
    change ‖w - 0‖ ≤ R
    rw [sub_zero]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    fin_cases i
    · change |x 2| ≤ R
      rw [abs_of_nonneg hn.1]
      exact le_max_left _ _
    all_goals simpa [w] using hR
  have hdiff (z : RestartState) (hz : z ∈ S) : DifferentiableAt ℝ restartCompactField z := by
    have hzR : ‖z‖ ≤ R := by simpa [S] using hz
    have H := (restartCompact_box_bounds (hzR.trans hRsmall)).2.1
    exact (contDiffAt_restartCompactField (by linarith only [H]) 1).differentiableAt (by norm_num)
  have hbound (z : RestartState) (hz : z ∈ S) : ‖fderiv ℝ restartCompactField z‖ ≤ C * R := by
    have hzR : ‖z‖ ≤ R := by simpa [S] using hz
    exact (hF z (hzR.trans hRsmall)).trans (mul_le_mul_of_nonneg_left hzR hC)
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_closedBall (0 : RestartState) R) hwS hxS
  have hdist : ‖restartPhysicalCoordinates x - w‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (restartCenterProjection x))).mpr
    intro i
    fin_cases i
    · change |x 2 - x 2| ≤ r
      simpa only [sub_self, abs_zero] using norm_nonneg (restartCenterProjection x)
    · change |x 1 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 0
    · change |x 3 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 1
    · change |x 4 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 2
  have hzero : restartCompactCenterProjection (restartCompactField w) = 0 := by
    ext i
    fin_cases i <;> simp [restartCompactCenterProjection, restartCompactField, w, shearMinus]
  rw [← (restartCompactField_physical hc hp).2]
  have heq : restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x)) =
      restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x) - restartCompactField w) := by
    rw [map_sub, hzero, sub_zero]
  rw [heq]
  exact (restartCompactCenterProjection_norm_le _).trans
    (H.trans ((mul_le_mul_of_nonneg_left hdist (mul_nonneg hC hR)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRsum hC) (norm_nonneg _))))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartFastBudget (C h b t : ℝ) :
    HasDerivAt (restartFastBudget C h b) (C * (h * Real.exp (-2 * t) + b)) t := by
  convert! (((((hasDerivAt_id' t).const_mul (-2)).exp.const_sub 1).const_mul (h / 2)).add
    ((hasDerivAt_id' t).const_mul b)).const_mul C using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastBudget_zero (C h b : ℝ) : restartFastBudget C h b 0 = 0 := by
  simp [restartFastBudget]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastBudget_le {C h b T t : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (ht : t ≤ T) : restartFastBudget C h b t ≤ C * h / 2 + C * b * T := by
  have H := mul_nonneg (mul_nonneg hC hh) (Real.exp_pos (-2 * t)).le
  have Ht := mul_le_mul_of_nonneg_left ht (mul_nonneg hC hb)
  dsimp only [restartFastBudget]
  nlinarith only [H, Ht]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exp_one_quarter_lt_two : Real.exp (1 / 4 : ℝ) < 2 := by
  have H := Real.exp_lt_two_add_div_two_sub (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restart_fastLayer_prefix {C h b T : ℝ} {α : ℝ → NormalizedState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 2 * h ≤ 1 / 16) (hb : b ≤ 1 / 16)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 < α t 2)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, restartControlRegion h b (α t))
    (hinit : α 0 2 ≤ h) :
    ∀ t ∈ Icc (0 : ℝ) T,
      α t 2 ≤ h * Real.exp (-2 * t) ∧ α t 0 ≤ -(15 / 16) ∧
        ‖restartCenterProjection (α t)‖ ≤
          ‖restartCenterProjection (α 0)‖ * Real.exp (restartFastBudget C h b t) := by
  have hbox (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖restartPhysicalCoordinates (α t)‖ ≤ 1 / 16 :=
    restartPhysicalCoordinates_norm_le (by norm_num)
      (by rw [abs_of_pos (hn t ht)]; exact (hregion t ht).2.1.trans hh) ((hregion t ht).2.2.trans hb)
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 < 0 := by
    have H := (hregion t ht).1
    linarith only [H]
  have hdecay (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 2 ≤ h * Real.exp (-2 * t) := by
    have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :=
      (hasDerivAt_normalized_components (hα s ⟨hs.1, hs.2.trans ht.2⟩)).2.2.1
    have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
        rateOne (α s 0) (α s 1) * α s 2 ≤ -2 * α s 2 := by
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have H := (restartCompact_box_bounds (hbox s hsT)).2.2.2.2.2.2
      rw [(restartCompactField_physical (hc s hsT) (hp s hsT)).1] at H
      exact mul_le_mul_of_nonneg_right H.le (hn s hsT).le
    have H := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) t) HD HB
      (s := 0) (t := t) ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
    have H' : α t 2 ≤ α 0 2 * Real.exp (-2 * t) := by simpa only [sub_zero] using H
    exact H'.trans (mul_le_mul_of_nonneg_right hinit (Real.exp_pos _).le)
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun s => restartCenterProjection (α s))
        (restartCenterProjection (normalizedField (α t))) t := by
    convert! restartCenterProjection.hasFDerivAt.comp_hasDerivAt t (hα t ht) using 1
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖restartCenterProjection (normalizedField (α t))‖ ≤
        (C * (h * Real.exp (-2 * t) + b)) * ‖restartCenterProjection (α t)‖ := by
    have H := restartCenterField_bound hC hF (hc t ht) (hp t ht)
      ⟨(hn t ht).le, (hregion t ht).2.1.trans hh⟩ ((hregion t ht).2.2.trans hb)
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (hdecay t ht) (hregion t ht).2.2) hC) (norm_nonneg _))
  have HG := norm_le_exp_of_norm_deriv_clock HD (fun t _ => hasDerivAt_restartFastBudget C h b t) HB
  intro t ht
  refine ⟨hdecay t ht, restartPhysical_shear_bound (hc t ht) (hp t ht) (hbox t ht), ?_⟩
  simpa only [restartFastBudget_zero, sub_zero] using HG t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_restartControlRegion (h b : ℝ) : IsClosed {x | restartControlRegion h b x} :=
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le (continuous_apply 2) continuous_const).inter
      (isClosed_le restartCenterProjection.continuous.norm continuous_const))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_restart_fastLayer_control {C h b T : ℝ} {x : NormalizedState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (_hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hn : 0 < x 2 ∧ x 2 ≤ h)
    (hZ : ‖restartCenterProjection x‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let y := normalizedMaxCurve x 0 t
      0 < y 2 ∧ y 2 ≤ h * Real.exp (-2 * t) ∧ y 0 ≤ -(15 / 16) ∧
        ‖restartCenterProjection y‖ ≤ ‖restartCenterProjection x‖ * Real.exp (restartFastBudget C h b t) ∧
        ‖restartCenterProjection y‖ < b := by
  let α := normalizedMaxCurve x 0
  let S := {t : ℝ | restartControlRegion h b (α t)}
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (normalizedField (α t)) t :=
    (normalizedMaxCurve_forward_of_constraint hc ht).1
  have hcon (t : ℝ) (ht : 0 ≤ t) : stateConstraint (α t) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < α t 2 := by
    have H := normalizedMaxCurve_wall_sign hc ht (0 : Fin 3)
    change (α t 2 = 0 ↔ x 2 = 0) ∧ (0 ≤ α t 2 ↔ 0 ≤ x 2) at H
    have hne : α t 2 ≠ 0 := fun he => hn.1.ne' (H.1.mp he)
    exact lt_of_le_of_ne (H.2.mpr hn.1.le) hne.symm
  have hinit : α 0 = x := normalizedMaxCurve_initial x 0
  have hhsmall : 2 * h ≤ 1 / 16 := by linarith only [hh.2]
  have hZsmall : ‖restartCenterProjection x‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
  have hpx : x 0 ≤ -(15 / 16) := restartPhysical_shear_bound hc hp
    (restartPhysicalCoordinates_norm_le (by norm_num)
      (by rw [abs_of_pos hn.1]; linarith only [hn.2, hh.2]) hZsmall)
  have hS0 : (0 : ℝ) ∈ S := by
    change restartControlRegion h b (α 0)
    rw [hinit]
    exact ⟨by linarith only [hpx], by linarith only [hn.2, hh.1], by linarith only [hZ, hb.1]⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn (fun t (ht : t ∈ Icc (0 : ℝ) T) => hα t ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_restartControlRegion h b)
    convert! H using 1
    ext t
    change (restartControlRegion h b (α t) ∧ t ∈ Icc 0 T) ↔
      (t ∈ Icc 0 T ∧ restartControlRegion h b (α t))
    tauto
  have hstrict {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
      (HZ : ‖restartCenterProjection (α t)‖ ≤
        ‖restartCenterProjection (α 0)‖ * Real.exp (restartFastBudget C h b t)) :
      ‖restartCenterProjection (α t)‖ < b := by
    rw [hinit] at HZ
    have HE := (restartFastBudget_le hC hh.1.le hb.1.le ht.2).trans hbudget
    have hbhalf : 0 < b / 2 := div_pos hb.1 (by norm_num)
    have H := HZ.trans (mul_le_mul hZ (Real.exp_le_exp.mpr HE) (Real.exp_pos _).le hbhalf.le)
    have H' := mul_lt_mul_of_pos_left exp_one_quarter_lt_two hbhalf
    nlinarith only [H, H']
  have hwhole : Icc (0 : ℝ) T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
    intro t ht hbefore
    have H := restart_fastLayer_prefix hC hF hhsmall hb.2
      (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hpos u hu.1)
      (fun u hu => hbefore hu) (by rw [hinit]; exact hn.2) t ⟨ht.1, le_rfl⟩
    have hpstrict : α t 0 < -(1 / 2) := by linarith only [H.2.1]
    have hnstrict : α t 2 < 2 * h := by
      have he := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
      have Hn := H.1.trans (mul_le_mul_of_nonneg_left he hh.1.le)
      nlinarith only [Hn, hh.1]
    have hZstrict := hstrict ⟨ht.1, ht.2.le⟩ H.2.2
    have hpcont := (continuous_apply (0 : Fin 5)).continuousAt.comp (hα t ht.1).continuousAt
    have hncont := (continuous_apply (2 : Fin 5)).continuousAt.comp (hα t ht.1).continuousAt
    have hZcont := (restartCenterProjection.continuous.continuousAt.comp (hα t ht.1).continuousAt).norm
    have Hev : ∀ᶠ u in 𝓝 t, u ∈ S := by
      filter_upwards [hpcont.eventually (isOpen_Iio.mem_nhds hpstrict),
        hncont.eventually (isOpen_Iio.mem_nhds hnstrict),
        hZcont.eventually (isOpen_Iio.mem_nhds hZstrict)] with u hpu hnu hZu
      exact ⟨hpu.le, hnu.le, hZu.le⟩
    exact Hev.filter_mono nhdsWithin_le_nhds
  have H := restart_fastLayer_prefix hC hF hhsmall hb.2
    (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hpos u hu.1)
    (fun u hu => hwhole hu) (by rw [hinit]; exact hn.2)
  intro t ht
  have Ht := H t ht
  refine ⟨hpos t ht.1, Ht.1, Ht.2.1, ?_, hstrict ht Ht.2.2⟩
  simpa only [hinit] using Ht.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_normalized_restart_fastLayer_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (x : NormalizedState),
      (0 < h ∧ h ≤ 1 / 128) → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T →
      C * h / 2 + C * b * T ≤ 1 / 4 → stateConstraint x = 1 → x 0 < 0 →
      (0 < x 2 ∧ x 2 ≤ h) → ‖restartCenterProjection x‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        let y := normalizedMaxCurve x 0 t
        0 < y 2 ∧ y 2 ≤ h * Real.exp (-2 * t) ∧ y 0 ≤ -(15 / 16) ∧
          ‖restartCenterProjection y‖ ≤ ‖restartCenterProjection x‖ * Real.exp (restartFastBudget C h b t) ∧
          ‖restartCenterProjection y‖ < b := by
  obtain ⟨A, _, HA⟩ := exists_restartCompact_derivative_bounds
  let C := max A 32
  have hC : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) (le_max_right A 32)
  have hF (w : RestartState) (hw : ‖w‖ ≤ 1 / 16) : ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖ :=
    (HA w hw).1.trans (mul_le_mul_of_nonneg_right (le_max_left A 32) (norm_nonneg w))
  exact ⟨C, le_max_right _ _, fun _ _ _ _ => normalized_restart_fastLayer_control hC hF⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSection_fastLayer_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T →
      C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        let x := normalizedMaxCurve (restartSectionChart h Z) 0 t
        0 < x 2 ∧ x 2 ≤ h * Real.exp (-2 * t) ∧ x 0 ≤ -(15 / 16) ∧
          ‖restartSectionCenterFlow h t Z‖ ≤ ‖Z‖ * Real.exp (restartFastBudget C h b t) ∧
          ‖restartSectionCenterFlow h t Z‖ < b := by
  obtain ⟨C, hC, HC⟩ := exists_normalized_restart_fastLayer_control
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  let w : RestartState := ![h, Z 0, Z 1, Z 2]
  have hw : ‖w‖ ≤ 1 / 16 := by
    have hZsmall : ‖Z‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    fin_cases i
    · change |h| ≤ 1 / 16
      rw [abs_of_pos hh]
      linarith only [hhsmall]
    · exact (norm_le_pi_norm Z 0).trans hZsmall
    · exact (norm_le_pi_norm Z 1).trans hZsmall
    · exact (norm_le_pi_norm Z 2).trans hZsmall
  have hr : 0 < restartSectionRadicand h Z := by
    have H := (restartCompact_box_bounds hw).2.1
    change 246 / 256 ≤ restartSectionRadicand h Z at H
    linarith only [H]
  have hp : restartSectionChart h Z 0 < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr hr)
  have hbudget : C * h / 2 + C * b * T ≤ 1 / 4 := by linarith only [hCh, hCb]
  have H := HC h b T (restartSectionChart h Z) ⟨hh, hhsmall⟩ hb hT hbudget
    (restartSectionChart_constraint hr.le) hp ⟨hh, le_rfl⟩
    (by simpa only [restartCenterProjection_section] using hZ)
  intro t ht
  simpa only [restartCenterProjection_section, restartSectionCenterFlow] using H t ht

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedChart_section {h : ℝ} (hh : 0 < h) (Z : RestartCenterState) :
    restartMixedChart (restartMixedSection h Z) = restartSectionChart h Z := by
  ext i
  fin_cases i <;> simp [restartMixedChart, restartMixedSection, restartSectionChart,
    restartCompactRoot, restartRadicand, restartExpCoordinates, restartSectionRadicand, Real.exp_log hh]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_physical {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionMixedFlow h t Z =
      restartMixedCoordinates (normalizedMaxCurve (restartSectionChart h Z) 0 t) := by
  rw [restartSectionMixedFlow, restartMixedFlow, restartMixedChart_section hh]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_center {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartCompactCenterProjection (restartSectionMixedFlow h t Z) = restartSectionCenterFlow h t Z := by
  rw [restartSectionMixedFlow_physical hh]
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactCenterProjection_comp_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] RestartState) :
    ‖restartCompactCenterProjection.comp L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  exact (restartCompactCenterProjection_norm_le (L v)).trans (L.le_opNorm v)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_restartSectionCenterFlow_of_mixed {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionCenterFlow h t)
      (restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) Z := by
  have H := restartCompactCenterProjection.hasFDerivAt.comp Z HD.hasFDerivAt
  simpa only [Function.comp_def, restartSectionMixedFlow_center hh] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadicand_pos_of_small {h : ℝ} {Z : RestartCenterState}
    (hh : |h| ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) : 0 < restartSectionRadicand h Z := by
  have hw := restartPhysicalCoordinates_norm_le (x := restartSectionChart h Z) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hh (by rwa [restartCenterProjection_section])
  have H := (restartCompact_box_bounds hw).2.1
  change 246 / 256 ≤ restartSectionRadicand h Z at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionStrongWall {h t : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z)
    (ht : t ∈ normalizedMaxDomain (restartSectionChart h Z) 0) :
    ContDiffAt ℝ 2 (restartSectionStrongWall h t) Z := by
  have H : ContDiffAt ℝ 2
      (fun W => normalizedMaxCurve (restartSectionChart h W) 0 t) Z :=
    (contDiffAt_normalizedMaxCurve_two ht).comp Z
      (g := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
      ((contDiffAt_restartSectionChart hZ 2).prodMk (contDiffAt_const (c := t)))
  exact (contDiffAt_apply ℝ ℝ (2 : Fin 5) _).comp Z H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongWall_pos {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 ≤ restartSectionRadicand h Z) (ht : 0 ≤ t) :
    0 < restartSectionStrongWall h t Z := by
  have H := normalizedMaxCurve_wall_sign (restartSectionChart_constraint hZ) ht (0 : Fin 3)
  change (restartSectionStrongWall h t Z = 0 ↔ h = 0) ∧
    (0 ≤ restartSectionStrongWall h t Z ↔ 0 ≤ h) at H
  have hne : restartSectionStrongWall h t Z ≠ 0 := fun he => hh.ne' (H.1.mp he)
  exact lt_of_le_of_ne (H.2.mpr hh.le) hne.symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongLog_eq {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionStrongLog h t Z = restartSectionMixedFlow h t Z 0 := by
  rw [restartSectionMixedFlow_physical hh]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_restartSectionStrongLog {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionStrongLog h t)
      ((ContinuousLinearMap.proj (0 : Fin 4)).comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) Z := by
  have H := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) (restartSectionMixedFlow h t Z)).comp Z HD.hasFDerivAt
  convert! H using 1
  ext W
  exact restartSectionStrongLog_eq hh t W

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongLog_fderiv_norm_le {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ ≤ ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ := by
  rw [(hasFDerivAt_restartSectionStrongLog hh HD).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (norm_le_pi_norm (fderiv ℝ (restartSectionMixedFlow h t) Z v) 0).trans
    ((fderiv ℝ (restartSectionMixedFlow h t) Z).le_opNorm v)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_restartSectionStrongWall {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionStrongWall h t)
      (restartSectionStrongWall h t Z • fderiv ℝ (restartSectionStrongLog h t) Z) Z := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hZ.le) 0 ht
  have hn := restartSectionStrongWall_pos hh hZ.le ht
  have Hlog := (hasFDerivAt_restartSectionStrongLog hh HD).differentiableAt.hasFDerivAt
  have HE := Hlog.exp
  have heq : (fun W => Real.exp (restartSectionStrongLog h t W)) =ᶠ[𝓝 Z] restartSectionStrongWall h t := by
    filter_upwards [(contDiffAt_restartSectionStrongWall hZ hdom).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hn)] with W hW
    exact Real.exp_log hW
  have H := HE.congr_of_eventuallyEq heq.symm
  simpa only [restartSectionStrongLog, Real.exp_log hn] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongWall_fderiv_norm {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ =
      restartSectionStrongWall h t Z * ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ := by
  rw [(hasFDerivAt_restartSectionStrongWall hh hZ ht HD).fderiv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (restartSectionStrongWall_pos hh hZ.le ht)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionRadialState_derivative {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z)
    (HB : ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ ≤ 2)
    (hn : restartSectionStrongWall h t Z ≤ 1) :
    DifferentiableAt ℝ (restartSectionRadialState h t) Z ∧
      ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2 ∧
      ∀ v : RestartCenterState,
        |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤
          2 * restartSectionStrongWall h t Z * ‖v‖ := by
  have Hn := hasFDerivAt_restartSectionStrongWall hh hZ ht HD
  have HZ := hasFDerivAt_restartSectionCenterFlow_of_mixed hh HD
  have HP := Hn.prodMk HZ
  change HasFDerivAt (restartSectionRadialState h t) _ Z at HP
  have hnpos := restartSectionStrongWall_pos hh hZ.le ht
  have Hlog := (restartSectionStrongLog_fderiv_norm_le hh HD).trans HB
  have hnD : ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ ≤ 2 * restartSectionStrongWall h t Z := by
    rw [restartSectionStrongWall_fderiv_norm hh hZ ht HD]
    nlinarith only [mul_le_mul_of_nonneg_left Hlog hnpos.le]
  have hZD : ‖fderiv ℝ (restartSectionCenterFlow h t) Z‖ ≤ 2 := by
    rw [HZ.fderiv]
    exact (restartCompactCenterProjection_comp_norm_le _).trans HB
  have hfst (v : RestartCenterState) :
      |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤ 2 * restartSectionStrongWall h t Z * ‖v‖ := by
    rw [HP.fderiv]
    change |(restartSectionStrongWall h t Z • fderiv ℝ (restartSectionStrongLog h t) Z) v| ≤ _
    rw [← Hn.fderiv]
    exact ((fderiv ℝ (restartSectionStrongWall h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hnD (norm_nonneg _))
  refine ⟨HP.differentiableAt, ?_, hfst⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [Prod.norm_def, max_le_iff]
  constructor
  · exact (hfst v).trans (by nlinarith only [mul_le_mul_of_nonneg_right hn (norm_nonneg v)])
  · rw [HP.fderiv]
    change ‖(restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) v‖ ≤ _
    rw [← HZ.fderiv]
    exact ((fderiv ℝ (restartSectionCenterFlow h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hZD (norm_nonneg _))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartShearCurve (σ n₂ n₃ ρ : ℝ) :
    HasDerivAt (restartShearCurve σ n₂ n₃) (restartShearDirection σ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartShearCurve, restartShearDirection] using (hasDerivAt_id ρ).const_mul σ
  · convert! hasDerivAt_const ρ n₂ using 1
  · convert! hasDerivAt_const ρ n₃ using 1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearDirection_norm {σ : ℝ} (hσ : |σ| = 1) :
    ‖restartShearDirection σ‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> simp [restartShearDirection, hσ]
  · simpa only [restartShearDirection, Matrix.cons_val_zero, Real.norm_eq_abs, hσ] using
      norm_le_pi_norm (restartShearDirection σ) 0

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearCurve_annulus {a ρ σ ε n₂ n₃ : ℝ} (ha : 0 < a)
    (hρ : ρ ∈ Icc a (2 * a)) (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) :
    ‖restartShearCurve σ n₂ n₃ ρ‖ ≤ 2 * a ∧
      a ≤ restartRadialNorm (restartShearCurve σ n₂ n₃ ρ) ∧ |n₂ - n₃| ≤ 2 * ε * a := by
  have hρpos := ha.trans_le hρ.1
  have hsmall : 2 * ε * a ≤ 2 * a := by nlinarith only [hε.2, ha]
  refine ⟨?_, ?_, abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * a)).mpr
    intro i
    fin_cases i
    · change |σ * ρ| ≤ 2 * a
      simpa only [abs_mul, hσ, abs_of_pos hρpos, one_mul] using hρ.2
    · exact (show |n₂| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₂.1] using h₂.2).trans hsmall
    · exact (show |n₃| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₃.1] using h₃.2).trans hsmall
  · have H := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (n₂ - n₃)) :
        (σ * ρ) ^ 2 ≤ (σ * ρ) ^ 2 + (n₂ - n₃) ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_mul, hσ, abs_of_pos hρpos, one_mul] at H
    exact hρ.1.trans H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadialState_center_fderiv {h T : ℝ} {Z : RestartCenterState}
    (H : DifferentiableAt ℝ (restartSectionRadialState h T) Z) (i : Fin 3) (v : RestartCenterState) :
    fderiv ℝ (fun W => restartSectionCenterFlow h T W i) Z v =
      (fderiv ℝ (restartSectionRadialState h T) Z v).2 i := by
  have HD := (ContinuousLinearMap.proj i).hasFDerivAt.comp Z
    ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp Z H.hasFDerivAt)
  change HasFDerivAt (fun W => restartSectionCenterFlow h T W i) _ Z at HD
  rw [HD.fderiv]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearCurve_sharp_control :
    ∃ C ≥ (32 : ℝ), ∀ h a T : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < a ∧ a ≤ 1) →
      8 * a ≤ 1 / 16 → 0 ≤ T → C * (8 * a) * T ≤ 1 / 8 →
      ∀ ε σ n₂ n₃ ρ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ρ ∈ Icc a (2 * a) →
          let Z := restartShearCurve σ n₂ n₃ ρ
          let p := restartSectionRadialState h T Z
          let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
          HasDerivAt (fun x => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ x)) v ρ ∧
          normalizedMaxCurve (restartSectionChart h Z) 0 T 0 ≤ -(15 / 16) ∧
          0 < p.1 ∧ p.1 ≤ h * Real.exp (-2 * T) ∧ ‖p.2‖ ≤ 8 * a ∧
          ‖v‖ ≤ 2 ∧ |v.1| ≤ 2 * p.1 ∧
          ∀ i : Fin 2, Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
            |v.2 i.succ| ≤ 8 * C * T * p.2 i.succ := by
  obtain ⟨A, _, HA⟩ := exists_restartSection_fastLayer_control
  obtain ⟨B, _, HB⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨D, hD, HD⟩ := exists_restartSectionWeakWall_derivative
  let C := max A (max B D)
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B D).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right B D).trans (le_max_right _ _)
  have hC : 32 ≤ C := hD.trans hDC
  have hC₀ : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨C, hC, ?_⟩
  intro h a T hh hCh ha hb hT hCb ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ
  let b := 8 * a
  let Z := restartShearCurve σ n₂ n₃ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
  have hbpos : 0 < b := by dsimp only [b]; positivity [ha.1]
  have hZ := (restartShearCurve_annulus ha.1 hρ hσ hε h₂ h₃).1
  have hZstrict : ‖Z‖ < b / 2 := by dsimp only [b]; linarith only [hZ, ha.1]
  have hbudget (E : ℝ) (hEC : E ≤ C) : E * h ≤ 1 / 4 ∧ E * b * T ≤ 1 / 8 :=
    ⟨(mul_le_mul_of_nonneg_right hEC hh.le).trans hCh,
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEC hbpos.le) hT).trans hCb⟩
  have HF := HA h b T Z hh (hbudget A hAC).1 ⟨hbpos, hb⟩ hT (hbudget A hAC).2 hZstrict.le T ⟨hT, le_rfl⟩
  have HM := (HB h b T hh (hbudget B hBC).1 ⟨hbpos, hb⟩ hT (hbudget B hBC).2 T ⟨hT, le_rfl⟩).1 Z hZstrict.le
  have HW (i : Fin 2) := HD h b T hh (hbudget D hDC).1 ⟨hbpos, hb⟩ hT (hbudget D hDC).2 Z hZstrict i
  have hhsmall : h ≤ 1 / 16 := by nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZstrict.le, hb])
  have hn : restartSectionStrongWall h T Z ≤ 1 := by
    have Hexp : Real.exp (-2 * T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hT])
    change normalizedMaxCurve (restartSectionChart h Z) 0 T 2 ≤ 1
    exact HF.2.1.trans ((mul_le_mul_of_nonneg_left Hexp hh.le).trans (by linarith only [hhsmall]))
  have HS := restartSectionRadialState_derivative hh hrad hT HM.1 (HM.2.trans exp_one_quarter_lt_two.le) hn
  have Hcurve := HS.1.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_restartShearCurve σ n₂ n₃ ρ)
  have hvnorm : ‖v‖ ≤ 2 := by
    have H := (fderiv ℝ (restartSectionRadialState h T) Z).le_opNorm (restartShearDirection σ)
    rw [restartShearDirection_norm hσ, mul_one] at H
    exact H.trans HS.2.1
  have hnpos : 0 < p.1 := HF.1
  refine ⟨Hcurve, HF.2.2.1, hnpos, HF.2.1, HF.2.2.2.2.le, hvnorm, ?_, ?_⟩
  · have H := HS.2.2 (restartShearDirection σ)
    rw [restartShearDirection_norm hσ, mul_one] at H
    exact H
  · intro i
    have hZi : 0 ≤ Z i.succ := by fin_cases i; exact h₂.1; exact h₃.1
    have hformula : p.2 i.succ = Z i.succ * restartSectionWeakMultiplier h T i Z := (HW i).1
    have hpi : 0 ≤ p.2 i.succ := by
      rw [hformula]
      exact mul_nonneg hZi (by linarith only [(HW i).2.1.1])
    change Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
      |v.2 i.succ| ≤ 8 * C * T * p.2 i.succ
    refine ⟨?_, ?_, ?_⟩
    · rw [hformula]
      nlinarith only [mul_le_mul_of_nonneg_left (HW i).2.1.1.le hZi]
    · rw [hformula]
      nlinarith only [mul_le_mul_of_nonneg_left (HW i).2.1.2.le hZi]
    · have H := (HW i).2.2.2 (restartShearDirection σ) (by fin_cases i <;> rfl)
      rw [restartSectionRadialState_center_fderiv HS.1, restartShearDirection_norm hσ, mul_one] at H
      change |v.2 i.succ| ≤ 8 * D * T * |p.2 i.succ| at H
      rw [abs_of_nonneg hpi] at H
      exact H.trans (by gcongr)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartShearInitialVariation_tangent {h ζ ν ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ)) :
    HasDerivAt (fun r => restartSectionChart h (restartShearCurve 1 ζ ν r))
      (restartShearInitialVariation h ζ ν ρ) ρ ∧
    normalizedConstraintDifferential (restartSectionChart h (restartShearCurve 1 ζ ν ρ))
      (restartShearInitialVariation h ζ ν ρ) = 0 := by
  have HD := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    ρ (hasDerivAt_restartShearCurve 1 ζ ν ρ)
  refine ⟨HD, ?_⟩
  have HR : Continuous (fun r => restartSectionRadicand h (restartShearCurve 1 ζ ν r)) := by
    unfold restartSectionRadicand restartShearCurve curvature
    fun_prop
  have HE : (fun r => stateConstraint (restartSectionChart h (restartShearCurve 1 ζ ν r))) =ᶠ[𝓝 ρ]
      fun _ => (1 : ℝ) := by
    filter_upwards [HR.continuousAt.eventually (isOpen_Ioi.mem_nhds hrad)] with r hr
    exact restartSectionChart_constraint hr.le
  exact ((hasFDerivAt_stateConstraint _).comp_hasDerivAt ρ HD).unique
    ((hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq HE)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartShearTailFlow {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0) :
    HasDerivAt (restartShearTailFlow h a q ζ ν t) (restartShearTailRadialVariation h a q ζ ν t ρ) ρ := by
  exact (hasFDerivAt_normalizedMaxCurve_initial ht).comp_hasDerivAt ρ
    (restartShearInitialVariation_tangent hrad).1

end
end

/-- The actual tail starts with a bounded shear derivative and only logarithmic wall response. -/
theorem solution :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q : ℝ, 2 < q → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < ζ ∧ ζ ≤ 2 * ε * a) → (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let z := restartShearTailFlow h a q ζ ν 0 ρ
          let v := restartShearTailRadialVariation h a q ζ ν 0 ρ
          a ≤ 1 ∧ 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ) ∧
          q / 2 * Real.log (1 / a) ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
          positiveWalls z ∧ |v 1| ≤ 2 ∧ shearTailLogSize z v ≤ 2 + 4 * C * q * |Real.log a| := by
  simp only [restartShearTailFlow, restartShearTailRadialVariation, zero_add]
  obtain ⟨C, hC, HC⟩ := exists_restartShearCurve_sharp_control
  obtain ⟨_, _, hF, hhF, HF⟩ := exists_restartShearFastEntry_control
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, min hF (1 / (4 * C)), lt_min hhF (by positivity), ?_⟩
  intro h hh q hq
  obtain ⟨aF, haF, HFa⟩ := HF h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  obtain ⟨aB, haB, HBa⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (eventually_restart_cutoff_budget C 4 q)
  refine ⟨min aF aB, lt_min haF haB, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ
  let T := q / 2 * Real.log (1 / a)
  let Z := restartShearCurve 1 ζ ν ρ
  let z := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let v := normalizedFlowDifferential (restartSectionChart h Z) 0 T (restartShearInitialVariation h ζ ν ρ)
  let p := restartSectionRadialState h T Z
  let w := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection 1)
  have HB := HBa ⟨ha.1, ha.2.trans (min_le_right _ _)⟩
  obtain ⟨ha1, hb, hT, hrad, hdom, _⟩ := HFa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    ε 1 ζ ν hε (by norm_num) ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp (hh.2.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨Hcurve, _, hn, _, _, hw, hwn, HW⟩ := HC h a T hh.1 hCh ⟨ha.1, ha1⟩ hb hT
    (by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using HB.2.2)
    ε 1 ζ ν ρ hε (by norm_num) ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ hρ
  have Hflow := hasDerivAt_restartShearTailFlow (a := a) (q := q) (t := 0) hrad
    (by simpa only [zero_add] using hdom)
  change HasDerivAt (fun r => normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 ζ ν r)) 0 (0 + T))
    (normalizedFlowDifferential (restartSectionChart h Z) 0 (0 + T) (restartShearInitialVariation h ζ ν ρ)) ρ at Hflow
  simp only [zero_add] at Hflow
  have Hs : w.2 0 = v 1 := (hasDerivAt_pi.mp Hcurve.snd 0).unique (hasDerivAt_pi.mp Hflow 1)
  have Hfst : HasDerivAt (fun r => (restartSectionRadialState h T (restartShearCurve 1 ζ ν r)).1) w.1 ρ := Hcurve.fst
  have Hn : w.1 = v 2 := Hfst.unique (hasDerivAt_pi.mp Hflow 2)
  have Hx : w.2 1 = v 3 := (hasDerivAt_pi.mp Hcurve.snd 1).unique (hasDerivAt_pi.mp Hflow 3)
  have Hy : w.2 2 = v 4 := (hasDerivAt_pi.mp Hcurve.snd 2).unique (hasDerivAt_pi.mp Hflow 4)
  have Hz : positiveWalls z := by
    refine ⟨hn, ?_, ?_⟩
    · exact (half_pos hζ.1).trans_le (HW 0).1
    · exact (half_pos hν.1).trans_le (HW 1).1
  have hcoef : 8 * C * T = 4 * C * q * |Real.log a| := by
    dsimp only [T]
    rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos ha.1.le ha1)]
    ring
  have hcoef0 : 0 ≤ 4 * C * q * |Real.log a| := by positivity [show 0 < q by linarith only [hq]]
  change |w.1| ≤ 2 * z 2 at hwn
  refine ⟨ha1, hrad, hdom, Hz, ?_, ?_⟩
  · change |v 1| ≤ 2
    rw [← Hs]
    exact ((norm_le_pi_norm w.2 0).trans (norm_snd_le w)).trans hw
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 + 4 * C * q * |Real.log a|)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_div]
    fin_cases i
    · change |v 2| / |z 2| ≤ _
      rw [abs_of_pos Hz.1, ← Hn]
      have H : |w.1| / z 2 ≤ 2 := (div_le_iff₀ Hz.1).mpr hwn
      exact H.trans (by linarith only [hcoef0])
    · change |v 3| / |z 3| ≤ _
      rw [abs_of_pos Hz.2.1, ← Hx]
      have H : |w.2 1| / z 3 ≤ 8 * C * T := (div_le_iff₀ Hz.2.1).mpr (HW 0).2.2
      rw [hcoef] at H
      linarith only [H]
    · change |v 4| / |z 4| ≤ _
      rw [abs_of_pos Hz.2.2, ← Hy]
      have H : |w.2 2| / z 4 ≤ 8 * C * T := (div_le_iff₀ Hz.2.2).mpr (HW 1).2.2
      rw [hcoef] at H
      linarith only [H]
