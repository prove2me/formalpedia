-- Prove2me | solution 1 for BianchiIX.exists_restartFastProjectionError_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:46:39.932936+00:00
-- url     : https://prove2.me/submissions/a348d8f5-47fd-4f44-b448-a14b2ce7a573

import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Theorems.Thm_BianchiIX_exists_compact_vanishing_slice_bounds
import Theorems.Thm_BianchiIX_exists_restartRadialCurve_control
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
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
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.MetricSpace.Thickening

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

private theorem BianchiIX.restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionPhase_eq_core {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hA : 0 < 1 + x 0) :
    restartProjectionPhase (x 2, ![x 1, x 3, x 4]) =
      2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2) := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcore : coreRadius (toProjectiveState x 0) (toProjectiveState x 2) =
      Real.sqrt ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * (x 3) ^ 2) / (1 + x 0) := by
    unfold coreRadius coreEnergy
    change Real.sqrt ((projectiveCoord (x 0) (x 1) - 1) ^ 2 +
      projectiveCoord (x 0) (x 3) ^ 2) = _
    have hid : (projectiveCoord (x 0) (x 1) - 1) ^ 2 + projectiveCoord (x 0) (x 3) ^ 2 =
        ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * (x 3) ^ 2) / (1 + x 0) ^ 2 := by
      unfold projectiveCoord
      field_simp
      nlinarith only [hsqrt]
    rw [hid, Real.sqrt_div (by positivity), Real.sqrt_sq hA.le]
  rw [restartProjectionPhase, restartProjectionHeight_of_constraint hc hp, hcore]
  change 2 * (1 + x 0) / Real.sqrt ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * x 3 ^ 2) = _
  rw [div_div_eq_mul_div]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.curvature_lower_of_active_dominance {n a b : ℝ} (ha : 0 < a)
    (hn : 0 ≤ n ∧ n ≤ a / 16) (hb : 0 ≤ b ∧ b ≤ a / 16) :
    3 / 4 * a ^ 2 ≤ curvature n a b := by
  have Hnb := mul_le_mul hn.2 hb.2 hb.1 (by positivity : 0 ≤ a / 16)
  have Hgap : 7 * a / 8 ≤ a - n - b := by linarith only [hn.2, hb.2]
  have Hsq := mul_self_le_mul_self (by positivity : 0 ≤ 7 * a / 8) Hgap
  unfold curvature
  nlinarith only [Hnb, Hsq]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_projective_height_pos_of_active_dominance {x : NormalizedState}
    (hc : stateConstraint x = 1) (ha : 0 < x 3)
    (hn : 0 ≤ x 2 ∧ x 2 ≤ x 3 / 16) (hb : 0 ≤ x 4 ∧ x 4 ≤ x 3 / 16) :
    0 < 1 + x 0 := by
  have H := curvature_lower_of_active_dominance ha hn hb
  have Hpos := sq_pos_of_pos ha
  dsimp only [stateConstraint, constraint, shearSq] at hc
  nlinarith only [H, Hpos, hc, sq_nonneg (x 1), sq_nonneg (x 0 + 1)]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionPhase_eq_core {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0)
    (hheight : 0 < 1 + normalizedMaxCurve (restartSectionChart h Z) 0 T 0) :
    (fun W => restartProjectionPhase (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => let x := normalizedMaxCurve (restartSectionChart h W) 0 T
        2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2)) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  have HnearR := HR.eventually (isOpen_Ioi.mem_nhds hrad)
  have HnearN := Hcoord.eventually (isOpen_Iio.mem_nhds hneg)
  have HnearA := (continuousAt_const.add Hcoord).eventually (isOpen_Ioi.mem_nhds hheight)
  filter_upwards [HnearR, HnearN, HnearA] with W hW hN hA
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionPhase_eq_core HC hN hA

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionDefect_scaled (p : RestartProjectionParameters) :
    restartProjectionDefect (restartProjectionScaledState p) =
      (p.1 0) ^ 2 * restartProjectionScaledDefect p := by
  unfold restartProjectionDefect restartProjectionScaledState restartProjectionScaledDefect curvature
  dsimp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_scaled (p : RestartProjectionParameters) :
    restartProjectionHeight (restartProjectionScaledState p) =
      (p.1 0) ^ 2 * restartProjectionScaledHeight p := by
  rw [restartProjectionHeight, restartProjectionDefect_scaled]
  unfold restartProjectionScaledHeight
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionPhase_scaled {p : RestartProjectionParameters} (hr : 0 < p.1 0) :
    restartProjectionPhase (restartProjectionScaledState p) -
      restartRadialPhase (restartProjectionScaledState p).2 =
        p.1 0 * restartProjectionScaledError p := by
  have hden : (Real.sqrt 3 * (restartProjectionScaledState p).2 0 -
      restartProjectionHeight (restartProjectionScaledState p)) ^ 2 +
      3 * ((restartProjectionScaledState p).2 1) ^ 2 =
        (p.1 0) ^ 2 * restartProjectionScaledDenom p := by
    rw [restartProjectionHeight_scaled]
    dsimp only [restartProjectionScaledState, restartProjectionScaledDenom]
    change (Real.sqrt 3 * (p.1 0 * p.2 0) - (p.1 0) ^ 2 * restartProjectionScaledHeight p) ^ 2 +
      3 * (p.1 0 * p.2 1) ^ 2 = _
    ring
  have hrad : restartRadialNorm (restartProjectionScaledState p).2 =
      p.1 0 * Real.sqrt ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) := by
    unfold restartRadialNorm
    change Real.sqrt ((p.1 0 * p.2 0) ^ 2 + (p.1 0 * p.2 1 - p.1 0 * p.1 2) ^ 2) = _
    rw [show (p.1 0 * p.2 0) ^ 2 + (p.1 0 * p.2 1 - p.1 0 * p.1 2) ^ 2 =
      (p.1 0) ^ 2 * ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]
  rw [restartProjectionPhase, hden, restartProjectionHeight_scaled,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le, restartRadialPhase, hrad]
  unfold restartProjectionScaledError
  rw [show 2 * (p.1 0 ^ 2 * restartProjectionScaledHeight p) =
    p.1 0 * (p.1 0 * (2 * restartProjectionScaledHeight p)) by ring,
    mul_div_mul_left _ _ hr.ne']
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionScaledError_axis (X : RestartProjectionCenter) :
    restartProjectionScaledError (0, X) = 0 := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hden : restartProjectionScaledDenom (0, X) = 3 * ((X 0) ^ 2 + (X 1) ^ 2) := by
    simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero, mul_pow, hsqrt]
    ring
  have hheight : restartProjectionScaledHeight (0, X) = ((X 0) ^ 2 + (X 1) ^ 2) / 2 := by
    norm_num [restartProjectionScaledHeight, restartProjectionScaledDefect, curvature]
  rw [restartProjectionScaledError, hden, hheight, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [Pi.zero_apply, sub_zero]
  let R := Real.sqrt ((X 0) ^ 2 + (X 1) ^ 2)
  have hR : R ^ 2 = (X 0) ^ 2 + (X 1) ^ 2 := Real.sq_sqrt (by positivity)
  change 2 * (((X 0) ^ 2 + (X 1) ^ 2) / 2) / (Real.sqrt 3 * R) - R / Real.sqrt 3 = 0
  rw [← hR]
  by_cases hR0 : R = 0
  · simp [hR0]
  · have h3 : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartProjectionScaledError {p : RestartProjectionParameters}
    (hr : 0 < 1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p)
    (hd : 0 < restartProjectionScaledDenom p)
    (hv : 0 < (p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError p := by
  have HD : ContDiffAt ℝ k restartProjectionScaledDefect p := by
    unfold restartProjectionScaledDefect curvature
    fun_prop
  have HR : ContDiffAt ℝ k (fun q : RestartProjectionParameters =>
      1 - (q.1 0) ^ 2 * restartProjectionScaledDefect q) p := by fun_prop
  have HA : ContDiffAt ℝ k restartProjectionScaledHeight p := by
    apply HD.div ((contDiffAt_const).add (HR.sqrt hr.ne'))
    exact ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p))
  have Hden : ContDiffAt ℝ k restartProjectionScaledDenom p := by
    unfold restartProjectionScaledDenom
    fun_prop
  apply ((contDiffAt_const.mul HA).div (Hden.sqrt hd.ne') (ne_of_gt (Real.sqrt_pos.mpr hd))).sub
  have HV : ContDiffAt ℝ k (fun q : RestartProjectionParameters =>
      (q.2 0) ^ 2 + (q.2 1 - q.1 2) ^ 2) p := by fun_prop
  exact (HV.sqrt hv.ne').div_const _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartProjectionScaledError_axis {X : RestartProjectionCenter}
    (hv : X 1 ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError (0, X) := by
  apply contDiffAt_restartProjectionScaledError
  · simp
  · simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero]
    have H := sq_pos_of_ne_zero hv
    nlinarith only [H, sq_nonneg (Real.sqrt 3 * X 0)]
  · simp only [Pi.zero_apply, sub_zero]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hv)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartProjectionScaledError_bounds {c M : ℝ} (hc : 0 < c) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ X : RestartProjectionCenter, |X 0| ≤ M → X 1 ∈ Icc c M →
        ∀ u : RestartProjectionNormal, ‖u‖ ≤ δ →
          ContDiffAt ℝ 2 restartProjectionScaledError (u, X) ∧
          |restartProjectionScaledError (u, X)| ≤ C * ‖u‖ ∧
          ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C ∧
          ∀ w : RestartProjectionCenter,
            |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖ := by
  let K : Set RestartProjectionCenter := Icc ![-M, c] ![M, M]
  have hK : IsCompact K := isCompact_Icc
  have hreg (X : RestartProjectionCenter) (hX : X ∈ K) :
      ContDiffAt ℝ 2 restartProjectionScaledError (0, X) := by
    have H : c ≤ X 1 := hX.1 1
    exact contDiffAt_restartProjectionScaledError_axis (ne_of_gt (hc.trans_le H)) 2
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_vanishing_slice_bounds hK hreg restartProjectionScaledError_axis
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro X hX₀ hX₁ u hu
  have hX : X ∈ K := by
    constructor
    · intro i
      fin_cases i
      · exact (abs_le.mp hX₀).1
      · exact hX₁.1
    · intro i
      fin_cases i
      · exact (abs_le.mp hX₀).2
      · exact hX₁.2
  exact H X hX u hu

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartProjectionScaledError_direction_bound {u du : RestartProjectionNormal}
    {X dX : RestartProjectionCenter} {C : ℝ}
    (HD : ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C)
    (HT : ∀ w : RestartProjectionCenter,
      |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖) :
    |fderiv ℝ restartProjectionScaledError (u, X) (du, dX)| ≤ C * ‖du‖ + C * ‖u‖ * ‖dX‖ := by
  have HN : |fderiv ℝ restartProjectionScaledError (u, X) (du, 0)| ≤ C * ‖du‖ := by
    have H := ((fderiv ℝ restartProjectionScaledError (u, X)).le_opNorm (du, 0)).trans
      (mul_le_mul_of_nonneg_right HD (norm_nonneg (du, (0 : RestartProjectionCenter))))
    simpa only [Real.norm_eq_abs, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg du)] using H
  have heq : (du, dX) = (du, (0 : RestartProjectionCenter)) + ((0 : RestartProjectionNormal), dX) := by simp
  rw [heq, map_add]
  exact (abs_add_le _ _).trans (add_le_add HN (HT dX))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionScaledState_parameters {r : ℝ} (hr : r ≠ 0) (p : RestartRadialState) :
    restartProjectionScaledState (restartProjectionParametersAt r p) = p := by
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · ext i
    fin_cases i <;> change r * (_ / r) = _ <;> field_simp <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionError_rescaled {r : ℝ} (hr : 0 < r) (p : RestartRadialState) :
    restartProjectionError p = r * restartProjectionScaledError (restartProjectionParametersAt r p) := by
  have H := restartProjectionPhase_scaled (p := restartProjectionParametersAt r p) hr
  rw [restartProjectionScaledState_parameters hr.ne'] at H
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_restartProjectionParametersAt (r : ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (restartProjectionParametersAt r) := by
  unfold restartProjectionParametersAt
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ k (fun _ : RestartRadialState => r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.1 / r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 2 / r)
      fun_prop
  · apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 0 / r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 1 / r)
      fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartProjectionParametersAt {p : ℝ → RestartRadialState} {v : RestartRadialState}
    {t : ℝ} (H : HasDerivAt p v t) (r : ℝ) :
    HasDerivAt (fun s => restartProjectionParametersAt r (p s)) (restartProjectionParameterTangent r v) t := by
  have Hfst : HasDerivAt (fun s => (p s).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hsnd : HasDerivAt (fun s => (p s).2) v.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have HN : HasDerivAt (fun s => (restartProjectionParametersAt r (p s)).1)
      (restartProjectionParameterTangent r v).1 t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_const t r using 1
    · convert! Hfst.div_const r using 1
    · convert! (hasDerivAt_pi.mp Hsnd 2).div_const r using 1
  have HC : HasDerivAt (fun s => (restartProjectionParametersAt r (p s)).2)
      (restartProjectionParameterTangent r v).2 t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! (hasDerivAt_pi.mp Hsnd 0).div_const r using 1
    · convert! (hasDerivAt_pi.mp Hsnd 1).div_const r using 1
  exact HN.prodMk HC

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartProjectionError {r : ℝ} {p : RestartRadialState} (hr : 0 < r)
    (H : ContDiffAt ℝ 2 restartProjectionScaledError (restartProjectionParametersAt r p)) :
    ContDiffAt ℝ 2 restartProjectionError p := by
  have heq : restartProjectionError = fun q => r * restartProjectionScaledError (restartProjectionParametersAt r q) :=
    funext (restartProjectionError_rescaled hr)
  rw [heq]
  exact contDiffAt_const.mul (H.comp p (contDiff_restartProjectionParametersAt r 2).contDiffAt)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartProjectionError {p : ℝ → RestartRadialState} {v : RestartRadialState}
    {r t : ℝ} (hr : 0 < r) (Hp : HasDerivAt p v t)
    (H : DifferentiableAt ℝ restartProjectionScaledError (restartProjectionParametersAt r (p t))) :
    HasDerivAt (fun s => restartProjectionError (p s))
      (r * fderiv ℝ restartProjectionScaledError (restartProjectionParametersAt r (p t))
        (restartProjectionParameterTangent r v)) t := by
  have HD := (H.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_restartProjectionParametersAt Hp r)).const_mul r
  simpa only [Function.comp_apply, restartProjectionError_rescaled hr] using HD

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fderiv_restartProjectionError {r : ℝ} {p : RestartRadialState} (hr : 0 < r)
    (H : ContDiffAt ℝ 2 restartProjectionScaledError (restartProjectionParametersAt r p)) (v : RestartRadialState) :
    fderiv ℝ restartProjectionError p v = r *
      fderiv ℝ restartProjectionScaledError (restartProjectionParametersAt r p) (restartProjectionParameterTangent r v) := by
  have Hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p using 1
    simp
  have Hscaled : DifferentiableAt ℝ restartProjectionScaledError
      (restartProjectionParametersAt r (p + (0 : ℝ) • v)) := by simpa using H.differentiableAt (by norm_num)
  have H₁ := hasDerivAt_restartProjectionError hr Hline Hscaled
  have H₂ := ((contDiffAt_restartProjectionError hr H).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 Hline (by simp)
  apply H₂.unique
  convert! H₁ using 1
  simp

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartProjectionError_bounds {c M : ℝ} (hc : 0 < c) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ r : ℝ, 0 < r → r ≤ δ →
      ∀ p : RestartRadialState, |p.2 0| ≤ M * r → c * r ≤ p.2 1 → p.2 1 ≤ M * r →
        |p.1| ≤ δ * r → |p.2 2| ≤ δ * r →
        ContDiffAt ℝ 2 restartProjectionError p ∧
        |restartProjectionError p| ≤ C * (r ^ 2 + |p.1| + |p.2 2|) ∧
        ∀ D : ℝ, 0 ≤ D → ∀ v : RestartRadialState,
          |v.2 0| ≤ D → |v.2 1| ≤ D →
          |v.1| ≤ D * |p.1| / r → |v.2 2| ≤ D * |p.2 2| / r →
            |fderiv ℝ restartProjectionError p v| ≤
              2 * C * D * (r + |p.1| / r + |p.2 2| / r) := by
  obtain ⟨δ, hδ, C, hC, HC⟩ := exists_restartProjectionScaledError_bounds (M := M) hc
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro r hr hrδ p hs ha₀ ha₁ hn hb
  let u := (restartProjectionParametersAt r p).1
  let X := (restartProjectionParametersAt r p).2
  have hC₀ : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC
  have hu : ‖u‖ ≤ δ := by
    apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
    intro i
    fin_cases i
    · change |r| ≤ δ
      rwa [abs_of_pos hr]
    · change |p.1 / r| ≤ δ
      rw [abs_div, abs_of_pos hr]
      exact (div_le_iff₀ hr).mpr hn
    · change |p.2 2 / r| ≤ δ
      rw [abs_div, abs_of_pos hr]
      exact (div_le_iff₀ hr).mpr hb
  have hX₀ : |X 0| ≤ M := by
    change |p.2 0 / r| ≤ M
    rw [abs_div, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hs
  have hX₁ : X 1 ∈ Icc c M := ⟨(le_div_iff₀ hr).mpr ha₀, (div_le_iff₀ hr).mpr ha₁⟩
  have H := HC X hX₀ hX₁ u hu
  let a := r + |p.1| / r + |p.2 2| / r
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hua : ‖u‖ ≤ a := by
    apply (pi_norm_le_iff_of_nonneg ha).mpr
    intro i
    fin_cases i
    · change |r| ≤ a
      rw [abs_of_pos hr]
      dsimp only [a]
      linarith only [div_nonneg (abs_nonneg p.1) hr.le, div_nonneg (abs_nonneg (p.2 2)) hr.le]
    · change |p.1 / r| ≤ a
      rw [abs_div, abs_of_pos hr]
      dsimp only [a]
      linarith only [hr, div_nonneg (abs_nonneg (p.2 2)) hr.le]
    · change |p.2 2 / r| ≤ a
      rw [abs_div, abs_of_pos hr]
      dsimp only [a]
      linarith only [hr, div_nonneg (abs_nonneg p.1) hr.le]
  refine ⟨contDiffAt_restartProjectionError hr H.1, ?_, ?_⟩
  · rw [restartProjectionError_rescaled hr, abs_mul, abs_of_pos hr]
    calc
      _ ≤ r * (C * ‖u‖) := mul_le_mul_of_nonneg_left H.2.1 hr.le
      _ ≤ r * (C * a) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hua hC₀) hr.le
      _ = C * (r ^ 2 + |p.1| + |p.2 2|) := by dsimp only [a]; field_simp
  · intro D hD v hvs hva hvn hvb
    let du := (restartProjectionParameterTangent r v).1
    let dX := (restartProjectionParameterTangent r v).2
    have hdu : ‖du‖ ≤ (|v.1| + |v.2 2|) / r := by
      apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (|v.1| + |v.2 2|) / r)).mpr
      intro i
      fin_cases i
      · change |(0 : ℝ)| ≤ _
        rw [abs_zero]
        positivity
      · change |v.1 / r| ≤ _
        rw [abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hr.le
      · change |v.2 2 / r| ≤ _
        rw [abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) hr.le
    have hdX : ‖dX‖ ≤ D / r := by
      apply (pi_norm_le_iff_of_nonneg (div_nonneg hD hr.le)).mpr
      intro i
      fin_cases i
      · change |v.2 0 / r| ≤ _
        rw [abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right hvs hr.le
      · change |v.2 1 / r| ≤ _
        rw [abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right hva hr.le
    have Hv : |v.1| + |v.2 2| ≤ D * a := by
      dsimp only [a]
      have Hsmall := add_le_add hvn hvb
      simp only [mul_div_assoc] at Hsmall
      nlinarith only [Hsmall, mul_nonneg hD hr.le]
    have HB := restartProjectionScaledError_direction_bound (du := du) (dX := dX) H.2.2.1 H.2.2.2
    rw [fderiv_restartProjectionError hr H.1 v, abs_mul, abs_of_pos hr]
    calc
      _ ≤ r * (C * ‖du‖ + C * ‖u‖ * ‖dX‖) := mul_le_mul_of_nonneg_left HB hr.le
      _ ≤ r * (C * ((|v.1| + |v.2 2|) / r) + C * a * (D / r)) := by gcongr
      _ = C * (|v.1| + |v.2 2|) + C * a * D := by field_simp
      _ ≤ C * (D * a) + C * a * D := add_le_add (mul_le_mul_of_nonneg_left Hv hC₀) le_rfl
      _ = 2 * C * D * (r + |p.1| / r + |p.2 2| / r) := by dsimp only [a]; ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartRadialCurve (θ ζ ρ : ℝ) :
    HasDerivAt (restartRadialCurve θ ζ) (restartRadialDirection θ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartRadialCurve, restartRadialDirection] using (hasDerivAt_id ρ).const_mul θ
  · convert! hasDerivAt_id ρ using 1
  · simpa [restartRadialCurve, restartRadialDirection] using hasDerivAt_const ρ ζ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialCurve_annulus {r ρ θ ζ L : ℝ} (hr : 0 < r)
    (hρ : ρ ∈ Icc r (2 * r)) (hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    ‖restartRadialCurve θ ζ ρ‖ ≤ (2 * (L + 1)) * r ∧
      r / 2 ≤ restartRadialNorm (restartRadialCurve θ ζ ρ) := by
  have hρ0 : 0 < ρ := hr.trans_le hρ.1
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2 * (L + 1)) * r)).mpr
    intro i
    fin_cases i
    · change |θ * ρ| ≤ _
      rw [abs_mul, abs_of_pos hρ0]
      have H := mul_le_mul hθ hρ.2 hρ0.le hL
      nlinarith only [H, hr]
    · change |ρ| ≤ _
      rw [abs_of_pos hρ0]
      nlinarith only [hρ.2, mul_nonneg hL hr.le]
    · change |ζ| ≤ _
      rw [abs_of_nonneg hζ.1]
      nlinarith only [hζ.2, hr, mul_nonneg hL hr.le]
  · have hdiff : 0 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg (θ * ρ)) :
      (ρ - ζ) ^ 2 ≤ (θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    rw [Real.sqrt_sq hdiff] at H
    change r / 2 ≤ Real.sqrt ((θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    linarith only [H, hρ.1, hζ.2, hr]

end
end

/-- The geometric comparison (E.15) is instantiated on the exact flow with one cutoff for the whole curve. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let x := normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastProjectionError h T θ ζ) ρ ∧
            |restartFastProjectionError h T θ ζ ρ| ≤ K * r ^ 2 ∧
            |deriv (restartFastProjectionError h T θ ζ) ρ| ≤ K * r ∧
            0 < 1 + x 0 ∧
            (restartFastProjectionPhase h T θ ζ =ᶠ[𝓝 ρ]
              fun y => restartProjectionPhase (restartSectionRadialState h T (restartRadialCurve θ ζ y))) := by
  obtain ⟨C, hC, HC⟩ := exists_restartRadialCurve_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro h hh L hL
  have hhpos := hh.1
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    nlinarith only [H]
  have hhsmall : h ≤ 1 / 16 := by nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hhpos.le]
  let M := 8 * (L + 1)
  let D := 8 * C * (L + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  have hD : 1 ≤ D := by
    dsimp only [D]
    nlinarith only [hC, mul_nonneg hCpos.le hL]
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hdir : 2 * (L + 1) ≤ D := by
    dsimp only [D]
    nlinarith only [hL, mul_le_mul_of_nonneg_right hC (show 0 ≤ L + 1 by positivity)]
  obtain ⟨δ, hδ, A, hA, HA⟩ := exists_restartProjectionError_bounds (M := M) (by norm_num : (0 : ℝ) < 1 / 2)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let K := 8 * A * D
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro q hq
  have Hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ((0 < r ∧ r ≤ 1) ∧ M * r ≤ 1 / 16 ∧ C * (M * r) * (q / 2 * Real.log (1 / r)) ≤ 1 / 8) ∧
      r * (q / 2 * Real.log (1 / r)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C (4 * (L + 1)) q,
      eventually_restart_cutoff_budget 1 1 q] with r H₁ H₂
    have heq : 2 * (4 * (L + 1)) * r = M * r := by dsimp only [M]; ring
    rw [heq] at H₁
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨r₀, hr₀, Hr₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min r₀ (min (1 / 64) (δ / 2)), lt_min hr₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have Hr := Hr₀ ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrsmall : r ≤ 1 / 64 := (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrδ : r ≤ δ / 2 := (hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hrsmall, hr.1])⟩
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ hr.1).mpr (by linarith only [Hr.1.1.2])))
  have H := HC h r T L hhpos hCh Hr.1.1 hL Hr.1.2.1 hT Hr.1.2.2 Hr.2 θ ζ ρ hθ hζsmall hρ
  obtain ⟨Hcurve, hnegative, hnpos, hnexp, hcenter, hactive, hweak, hcv, hnv, hwv⟩ := H
  change HasDerivAt (fun x => restartSectionRadialState h T (restartRadialCurve θ ζ x)) v ρ at Hcurve
  change 0 < p.1 at hnpos
  change p.1 ≤ h * Real.exp (-2 * T) at hnexp
  change ‖p.2‖ ≤ M * r at hcenter
  change r / 2 ≤ p.2 1 at hactive
  change 0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ at hweak
  change ∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1) at hcv
  change |v.1| ≤ 2 * (L + 1) * p.1 / r at hnv
  change |v.2 2| ≤ D * p.2 2 / r at hwv
  have he : Real.exp (-2 * T) = r ^ q := by
    rw [Real.rpow_def_of_pos hr.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  have hpower : r ^ q ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 Hr.1.1.2 hq.le
  have hnsmall : p.1 ≤ r ^ 2 := by
    rw [he] at hnexp
    exact hnexp.trans ((mul_le_mul_of_nonneg_left hpower hhpos.le).trans
      (mul_le_of_le_one_left (sq_nonneg r) (by linarith only [hhsmall])))
  have hwsmall : p.2 2 ≤ 2 * r ^ 2 := hweak.2.trans (mul_le_mul_of_nonneg_left hζ.2 (by norm_num))
  have hgeom := HA r hr.1 (by linarith only [hrδ, hδ]) p
    ((norm_le_pi_norm p.2 0).trans hcenter) (by linarith only [hactive])
    ((le_abs_self _).trans ((norm_le_pi_norm p.2 1).trans hcenter))
    (by rw [abs_of_pos hnpos]; nlinarith only [hnsmall, mul_le_mul_of_nonneg_right hrδ hr.1.le])
    (by rw [abs_of_nonneg hweak.1]; nlinarith only [hwsmall, mul_le_mul_of_nonneg_right hrδ hr.1.le])
  have Hder := hgeom.2.2 D hDpos.le v ((hcv 0).trans hdir) ((hcv 1).trans hdir)
    (by rw [abs_of_pos hnpos]; exact hnv.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdir hnpos.le) hr.1.le))
    (by rwa [abs_of_nonneg hweak.1])
  have HD := (hgeom.1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt ρ Hcurve
  change HasDerivAt (restartFastProjectionError h T θ ζ) (fderiv ℝ restartProjectionError p v) ρ at HD
  have hZ := (restartRadialCurve_annulus hr.1 hρ hL hθ hζsmall).1
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hhpos]) (by
      change ‖Z‖ ≤ 2 * (L + 1) * r at hZ
      have Hb : 8 * (L + 1) * r ≤ 1 / 16 := Hr.1.2.1
      linarith only [hZ, Hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  have hxcon : stateConstraint x = 1 := (normalizedMaxCurve_forward_of_constraint
    (restartSectionChart_constraint hrad.le) hT).2.1
  have hxactive : 0 < x 3 := by change 0 < p.2 1; linarith only [hactive, hr.1]
  have hxstrong : 0 ≤ x 2 ∧ x 2 ≤ x 3 / 16 := by
    change 0 ≤ p.1 ∧ p.1 ≤ p.2 1 / 16
    exact ⟨hnpos.le, by nlinarith only [hnsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]⟩
  have hxweak : 0 ≤ x 4 ∧ x 4 ≤ x 3 / 16 := by
    change 0 ≤ p.2 2 ∧ p.2 2 ≤ p.2 1 / 16
    exact ⟨hweak.1, by nlinarith only [hwsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]⟩
  have hxheight := normalized_projective_height_pos_of_active_dominance hxcon hxactive hxstrong hxweak
  have hxnegative : x 0 < 0 := by change x 0 ≤ -(15 / 16) at hnegative; linarith only [hnegative]
  have Hnear := (eventually_restartSectionProjectionPhase_eq_core hrad hT hxnegative hxheight).comp_tendsto
    (hasDerivAt_restartRadialCurve θ ζ ρ).continuousAt
  refine ⟨hdom, HD.differentiableAt, ?_, ?_, hxheight, Hnear.symm⟩
  · change |restartProjectionError p| ≤ K * r ^ 2
    have HV := hgeom.2.1
    rw [abs_of_pos hnpos, abs_of_nonneg hweak.1] at HV
    have Hsmall := mul_le_mul_of_nonneg_left (add_le_add hnsmall hwsmall) hApos.le
    have HK : 4 * A ≤ K := by dsimp only [K]; nlinarith only [hApos, mul_le_mul_of_nonneg_left hD hApos.le]
    exact (HV.trans (by nlinarith only [Hsmall])).trans (mul_le_mul_of_nonneg_right HK (sq_nonneg r))
  · rw [HD.deriv]
    rw [abs_of_pos hnpos, abs_of_nonneg hweak.1] at Hder
    have Hn : p.1 / r ≤ r := (div_le_iff₀ hr.1).mpr (by nlinarith only [hnsmall])
    have Hw : p.2 2 / r ≤ 2 * r := (div_le_iff₀ hr.1).mpr (by nlinarith only [hwsmall])
    exact Hder.trans (by
      change 2 * A * D * (r + p.1 / r + p.2 2 / r) ≤ (8 * A * D) * r
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add Hn Hw) (show 0 ≤ 2 * A * D by positivity)])
