-- Prove2me | solution 1 for BianchiIX.compactConnectionFinitePhase_strong_reference
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:28:03.767444+00:00
-- url     : https://prove2.me/submissions/7305a8a1-7bbb-4383-98f2-f0c0b4a34269

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_coreTail_reference_regular
import Theorems.Thm_BianchiIX_coreTail_strong_variation_invariant
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
import Theorems.Thm_BianchiIX_stableResidualIntegral_bound
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Order.ProjIcc

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

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_zero {a : ℝ} (ha : 0 ≤ a) : phaseNorm a 0 = a := by
  simp [phaseNorm, Real.sqrt_sq ha]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_defect {a b : ℝ} (ha : 0 < a) :
    phaseNorm a b - a = b ^ 2 / (phaseNorm a b + a) := by
  apply (eq_div_iff (ne_of_gt (add_pos (phaseNorm_pos ha) ha))).mpr
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_defect {a b : ℝ} (ha : 0 < a) :
    1 - a / phaseNorm a b = b ^ 2 * phaseNormKernel a b := by
  have hn := ne_of_gt (phaseNorm_pos (b := b) ha)
  have hs := ne_of_gt (add_pos (phaseNorm_pos (b := b) ha) ha)
  dsimp [phaseNormKernel]
  field_simp
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_pos {m w : ℝ} (hm : -1 < m) : 0 < stableWeakRadius m w :=
  phaseNorm_pos (by linarith : 0 < m + 1)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_sq (m w : ℝ) :
    stableWeakRadius m w ^ 2 = (m + 1) ^ 2 + w ^ 2 := phaseNorm_sq _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrectedPhase_zero {m : ℝ} (hm : -1 ≤ m) :
    stableCorrectedPhase m 0 0 = m := by
  simp only [stableCorrectedPhase, stableWeakRadius, phaseNorm_zero (by linarith : 0 ≤ m + 1),
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectionA {m : ℝ} (hm : 1 < m) :
    HasDerivAt stableCorrectionA (-(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2) m := by
  have hd : m ^ 2 - 1 ≠ 0 := by nlinarith
  convert! (hasDerivAt_id m).div (((hasDerivAt_id m).pow 2).sub_const 1) hd using 1
  dsimp
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectionC {m : ℝ} (hm : -1 < m) :
    HasDerivAt stableCorrectionC (2 / (m + 1) ^ 2) m := by
  have hd : m + 1 ≠ 0 := by linarith
  convert! (hasDerivAt_const m (-2 : ℝ)).div ((hasDerivAt_id m).add_const 1) hd using 1
  simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableWeakRadius {m w : ℝ → ℝ} {m' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hw : HasDerivAt w w' t) (hpos : -1 < m t) :
    HasDerivAt (fun s => stableWeakRadius (m s) (w s))
      (((m t + 1) * m' + w t * w') / stableWeakRadius (m t) (w t)) t := by
  have hn : (m t + 1) ^ 2 + w t ^ 2 ≠ 0 := by
    have h : 0 < m t + 1 := by linarith
    positivity
  convert! ((((hm.add_const 1).pow 2).add (hw.pow 2)).sqrt hn) using 1
  dsimp [stableWeakRadius, phaseNorm]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectedPhase {m u w : ℝ → ℝ} {m' u' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hpos : 1 < m t) :
    HasDerivAt (fun s => stableCorrectedPhase (m s) (u s) (w s))
      (stableCorrectedGradient (m t) (u t) (w t) 0 * m' +
        stableCorrectedGradient (m t) (u t) (w t) 1 * u' +
        stableCorrectedGradient (m t) (u t) (w t) 2 * w') t := by
  have hS := hasDerivAt_stableWeakRadius hm hw (by linarith)
  have hA := (hasDerivAt_stableCorrectionA hpos).comp t hm
  have hC := (hasDerivAt_stableCorrectionC (by linarith : -1 < m t)).comp t hm
  convert! ((hS.sub_const 1).add (hA.mul (hu.pow 2))).add ((hC.mul hu).mul hw) using 1
  dsimp [stableCorrectedGradient]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_stableCorrectedPhase (n : WithTop ℕ∞) {y : Fin 3 → ℝ}
    (hm : 1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have hD : y 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  unfold stableCorrectedPhase stableWeakRadius phaseNorm stableCorrectionA stableCorrectionC
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_directional {m u w : ℝ} (hm : -1 < m) :
    (m + 1) / stableWeakRadius m w * phaseVelocity m u 0 w +
      w / stableWeakRadius m w * weakVelocity m u 0 w =
    (stableWeakRadius m w - (m + 1) / stableWeakRadius m w) * u ^ 2 -
      stableWeakRadius m w * u * w := by
  have hS := ne_of_gt (stableWeakRadius_pos (w := w) hm)
  rw [(stable_boundary_field m u w).1, (stable_boundary_field m u w).2.2.2]
  unfold stableWeakRate
  field_simp
  linear_combination -(u ^ 2 - u * w) * stableWeakRadius_sq m w

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_directional_quartic {m u w : ℝ} (hm : -1 < m) :
    (m + 1) / stableWeakRadius m w * phaseVelocity m u 0 w +
      w / stableWeakRadius m w * weakVelocity m u 0 w =
    m * u ^ 2 - (m + 1) * u * w +
      (stableWeakRadius m w + 1) / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1))) * u ^ 2 * w ^ 2 -
      1 / (stableWeakRadius m w + (m + 1)) * u * w ^ 3 := by
  have hL : 0 < m + 1 := by linarith
  have hS := ne_of_gt (stableWeakRadius_pos (w := w) hm)
  have hsum : stableWeakRadius m w + (m + 1) ≠ 0 :=
    ne_of_gt (add_pos (stableWeakRadius_pos hm) hL)
  have hd := phaseNorm_defect (b := w) hL
  have hr := phaseNorm_ratio_defect (b := w) hL
  change stableWeakRadius m w - (m + 1) = w ^ 2 / (stableWeakRadius m w + (m + 1)) at hd
  change 1 - (m + 1) / stableWeakRadius m w =
    w ^ 2 * (1 / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1)))) at hr
  rw [stableWeakRadius_directional hm]
  have hcoef : stableWeakRadius m w - (m + 1) / stableWeakRadius m w =
      m + (stableWeakRadius m w + 1) /
        (stableWeakRadius m w * (stableWeakRadius m w + (m + 1))) * w ^ 2 := by
    calc
      _ = m + (stableWeakRadius m w - (m + 1)) + (1 - (m + 1) / stableWeakRadius m w) := by ring
      _ = _ := by rw [hd, hr]; field_simp; ring
  rw [hcoef]
  calc
    _ = m * u ^ 2 - (m + 1) * u * w +
        (stableWeakRadius m w + 1) / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1))) * u ^ 2 * w ^ 2 -
        (stableWeakRadius m w - (m + 1)) * u * w := by ring
    _ = _ := by rw [hd]; ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrectedPhase_directional {m u w : ℝ} (hm : 1 < m) :
    stableCorrectedGradient m u w 0 * phaseVelocity m u 0 w +
      stableCorrectedGradient m u w 1 * strongVelocity m u 0 w +
      stableCorrectedGradient m u w 2 * weakVelocity m u 0 w = stableCorrectedResidual m u w := by
  have hD : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hL : m + 1 ≠ 0 := by linarith
  have H := stableWeakRadius_directional_quartic (u := u) (w := w) (by linarith : -1 < m)
  dsimp [stableCorrectedGradient, stableCorrectedResidual, stableResidual4,
    stableResidual3, stableResidual2, stableResidual1, stableCorrectionA, stableCorrectionC]
  calc
    _ = ((m + 1) / stableWeakRadius m w * phaseVelocity m u 0 w +
          w / stableWeakRadius m w * weakVelocity m u 0 w) +
        (-(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2 * u ^ 2 + 2 / (m + 1) ^ 2 * u * w) * phaseVelocity m u 0 w +
        (2 * (m / (m ^ 2 - 1)) * u + -2 / (m + 1) * w) * strongVelocity m u 0 w +
        (-2 / (m + 1) * u) * weakVelocity m u 0 w := by ring
    _ = _ := by
      rw [H]
      unfold phaseVelocity strongVelocity weakVelocity coupling
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

private theorem BianchiIX.hasDerivAt_stableBoundaryOrbit {m c u w t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (ht : 0 ≤ t) :
    HasDerivAt (stableBoundaryOrbit m u w)
      (normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 t •
        projectiveField (stableBoundaryOrbit m u w t)) t := by
  have hx := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have H := normalizedMaxCurve_forward_of_constraint hx ht
  have hK : 0 < c + 1 := by linarith
  have hA := lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2)
    (stableBoundaryOrbit_global hc hm hu hw t ht).1
  exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt hA) H.2.1

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
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableCorrectedPhase_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hm : 1 < Y t 0) (hv : Y t 2 = 0) :
    HasDerivAt (fun s => stableCorrectedPhase (Y s 0) (Y s 1) (Y s 3))
      (a * stableCorrectedResidual (Y t 0) (Y t 1) (Y t 3)) t := by
  have H := hasDerivAt_stableCorrectedPhase (hasDerivAt_pi.mp hY 0)
    (hasDerivAt_pi.mp hY 1) (hasDerivAt_pi.mp hY 3) hm
  convert! H using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  change _ = _ * (a * phaseVelocity _ _ _ _) + _ * (a * strongVelocity _ _ _ _) + _ * (a * weakVelocity _ _ _ _)
  rw [hv, ← stableCorrectedPhase_directional hm]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.contDiffAt_stableCorrectedResidual (n : WithTop ℕ∞) {y : Fin 3 → ℝ}
    (hm : 1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableCorrectedResidual (z 0) (z 1) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have hD : y 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hD2 := pow_ne_zero 2 hD
  have hL2 := pow_ne_zero 2 hL
  have hR : Real.sqrt ((y 0 + 1) ^ 2 + y 2 ^ 2) ≠ 0 :=
    ne_of_gt (stableWeakRadius_pos (w := y 2) (by linarith : -1 < y 0))
  have hsum : Real.sqrt ((y 0 + 1) ^ 2 + y 2 ^ 2) + (y 0 + 1) ≠ 0 := by
    have H := Real.sqrt_nonneg ((y 0 + 1) ^ 2 + y 2 ^ 2)
    linarith
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  have hprod := mul_ne_zero hR hsum
  unfold stableCorrectedResidual stableResidual4 stableResidual3 stableResidual2 stableResidual1
    stableWeakRadius phaseNorm
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableCorrectedApproximation_tendsto {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (fun t => stableCorrectedApproximation ![m, u, w] t) atTop (𝓝 (stableBoundaryProjection m u w)) := by
  have H := stableBoundaryProjection_exists hc hm hu hw
  have hP : 1 < stableBoundaryProjection m u w := by
    have hband := (abs_le.mp (stableBoundaryProjection_band hc hm hu hw)).1
    linarith
  have hvec : Tendsto (fun t => ![stableBoundaryOrbit m u w t 0, stableBoundaryOrbit m u w t 1,
      stableBoundaryOrbit m u w t 3]) atTop (𝓝 (![stableBoundaryProjection m u w, 0, 0] : Fin 3 → ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact H.1
    · exact H.2.1
    · exact H.2.2.1
  have hlim := (contDiffAt_stableCorrectedPhase 2 (y := ![stableBoundaryProjection m u w, 0, 0]) hP).continuousAt.tendsto.comp hvec
  change Tendsto (fun t => stableCorrectedApproximation ![m, u, w] t) atTop
    (𝓝 (stableCorrectedPhase (stableBoundaryProjection m u w) 0 0)) at hlim
  rw [stableCorrectedPhase_zero (by linarith : -1 ≤ stableBoundaryProjection m u w)] at hlim
  exact hlim

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableResidualIntegral_eq {m c u w T : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hT : 0 ≤ T) :
    stableResidualIntegral m u w T = stableCorrectedApproximation ![m, u, w] T - stableCorrectedPhase m u w := by
  let Y := stableBoundaryOrbit m u w
  let a := normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0
  have hM (t : ℝ) (ht : 0 ≤ t) : 1 < Y t 0 := by
    have hl := (abs_le.mp (stableBoundaryOrbit_global hc hm hu hw t ht).2.1.1).1
    linarith
  have hY (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_stableBoundaryOrbit hc hm hu hw ht
  have hd (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_stableCorrectedPhase_scaled
    (hY t ht) (hM t ht) (stableBoundaryOrbit_global hc hm hu hw t ht).2.1.2.2.1
  have hR : ContinuousOn (fun t => stableCorrectedResidual (Y t 0) (Y t 1) (Y t 3)) (Icc 0 T) := by
    intro t ht
    have hcoords : ContinuousAt (fun s => ![Y s 0, Y s 1, Y s 3]) t := by
      have H : ContinuousAt Y t := (hY t ht.1).continuousAt
      apply continuousAt_pi.mpr
      intro i
      fin_cases i
      · change ContinuousAt (fun s => Y s 0) t
        exact (continuous_apply 0).continuousAt.comp H
      · change ContinuousAt (fun s => Y s 1) t
        exact (continuous_apply 1).continuousAt.comp H
      · change ContinuousAt (fun s => Y s 3) t
        exact (continuous_apply 3).continuousAt.comp H
    have HC := (contDiffAt_stableCorrectedResidual 1 (y := ![Y t 0, Y t 1, Y t 3]) (hM t ht.1)).continuousAt.comp
      (f := fun s => ![Y s 0, Y s 1, Y s 3]) hcoords
    exact HC.continuousWithinAt
  have hx := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have ha : ContinuousOn a (Icc 0 T) := (continuousOn_normalizedProjectiveRate _ _).mono
    (fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht.1)
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (show 0 ≤ t from (uIcc_of_le hT ▸ ht).1))
    ((ha.mul hR).intervalIntegrable_of_Icc hT)
  change stableResidualIntegral m u w T =
    stableCorrectedApproximation ![m, u, w] T - stableCorrectedPhase (Y 0 0) (Y 0 1) (Y 0 3) at H
  simpa [Y, stableBoundaryOrbit_initial, stableBoundaryEntry] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableResidualIntegral_tendsto {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (stableResidualIntegral m u w) atTop (𝓝 (stableBoundaryProjection m u w - stableCorrectedPhase m u w)) := by
  apply ((stableCorrectedApproximation_tendsto hc hm hu hw).sub_const (stableCorrectedPhase m u w)).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (stableResidualIntegral_eq hc hm hu hw hT).symm

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
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_remainder {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    |stableBoundaryProjection m u w - stableCorrectedPhase m u w| ≤
      1024 * |u| * (|u| + |w|) ^ 3 / (c + 1) ^ 3 := by
  apply le_of_tendsto (stableResidualIntegral_tendsto hc hm hu hw).abs
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact stableResidualIntegral_bound hc hm hu hw hT

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_weak {m c w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hw : |w| ≤ 1 / 200) :
    stableBoundaryProjection m 0 w = stableWeakRadius m w - 1 := by
  have H := stableBoundaryProjection_remainder hc hm (by norm_num : |(0 : ℝ)| ≤ 1 / 200) hw
  have H0 : |stableBoundaryProjection m 0 w - (stableWeakRadius m w - 1)| ≤ 0 := by
    simpa [stableCorrectedPhase] using H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H0 (abs_nonneg _)))

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

private theorem BianchiIX.stableRescaledFlow_initial (K : ℝ) (y : StableState) : stableRescaledFlow K y 0 = y := by
  simp only [stableRescaledFlow, mul_zero, stableOriginalFlow_initial]

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

private theorem BianchiIX.hasDerivAt_stableRescaledFlow {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasDerivAt (stableRescaledFlow K y) (K • stableOriginalField (stableRescaledFlow K y s)) s := by
  exact (hasDerivAt_stableOriginalFlow hc hm hu hw (mul_nonneg hK.le hs)).scomp s
    (by simpa using (hasDerivAt_id s).const_mul K)

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
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledFlow_limit {K : ℝ} {y : StableState} {c : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Tendsto (stableRescaledFlow K y) atTop (𝓝 ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) :=
  (stableOriginalFlow_limit hc hm hu hw).comp (Tendsto.const_mul_atTop hK tendsto_id)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTail_reflected_reference {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    projectiveReflection (coreTailState η ![k, 0, 0]) =
      ![Real.sqrt (k ^ 2 - η ^ 2) - 1, 0, 0, η] := by
  rw [(coreTail_reference_regular hk hη).2.1]
  ext i
  fin_cases i <;> dsimp [projectiveReflection]
  ring

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

private theorem BianchiIX.stable_weak_linear_energy {y v : StableState} (hu : y 1 = 0) :
    stableOriginalField y 0 * v 0 +
      (y 0 + 1) * (stableOriginalJacobian y).mulVec v 0 +
      stableOriginalField y 2 * (v 2 - 2 * v 1) +
      y 2 * ((stableOriginalJacobian y).mulVec v 2 -
        2 * (stableOriginalJacobian y).mulVec v 1) = 0 := by
  simp [stableOriginalField, stableOriginalJacobian, stableBoundaryField,
    stableBoundaryJacobian, stableDenomGradient, stableStrongRate, stableWeakRate,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hu]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableRescaledFlow_strong_zero {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40) (hu : y 1 = 0)
    (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    stableRescaledFlow (c + 1) y s 1 = 0 := by
  have H := (stableBoundaryOrbit_global (u := y 1) hc hm (by rw [hu]; norm_num) hw
    ((c + 1) * s) (mul_nonneg (by linarith) hs)).2.2.2.1
  rw [hu, abs_zero] at H
  have heq := abs_eq_zero.mp (le_antisymm H (abs_nonneg _))
  simpa [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply, hu] using heq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableRescaledDifferential_weak_energy {y v : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40) (hu : y 1 = 0)
    (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    let z := stableRescaledFlow (c + 1) y s
    let q := stableRescaledDifferential (c + 1) y s v
    (z 0 + 1) * q 0 + z 2 * (q 2 - 2 * q 1) =
      (y 0 + 1) * v 0 + y 2 * (v 2 - 2 * v 1) := by
  let z := stableRescaledFlow (c + 1) y
  let q := fun t => stableRescaledDifferential (c + 1) y t v
  let E := fun t => (z t 0 + 1) * q t 0 + z t 2 * (q t 2 - 2 * q t 1)
  have hK : 0 < c + 1 := by linarith
  have hu' : |y 1| ≤ 1 / 200 := by rw [hu]; norm_num
  have hE (t : ℝ) (ht : t ∈ Icc 0 s) : HasDerivAt E 0 t := by
    have hz := hasDerivAt_pi.mp (hasDerivAt_stableRescaledFlow hK hc hm hu' hw ht.1)
    have hq := hasDerivAt_pi.mp (stableRescaledFlow_variational_equation hK hc hm hu' hw ht.1 v)
    have H := (((hz 0).add_const 1).mul (hq 0)).add
      ((hz 2).mul ((hq 2).sub ((hq 1).const_mul 2)))
    have Hz : z t 1 = 0 := stableRescaledFlow_strong_zero hc hm hu hw ht.1
    have HE := stable_weak_linear_energy (v := q t) Hz
    convert! H using 1
    change 0 = (c + 1) * stableOriginalField (z t) 0 * q t 0 +
      (z t 0 + 1) * ((c + 1) * (stableOriginalJacobian (z t)).mulVec (q t) 0) +
      ((c + 1) * stableOriginalField (z t) 2 * (q t 2 - 2 * q t 1) +
      z t 2 * ((c + 1) * (stableOriginalJacobian (z t)).mulVec (q t) 2 -
        2 * ((c + 1) * (stableOriginalJacobian (z t)).mulVec (q t) 1)))
    linear_combination -(c + 1) * HE
  have H := (convex_Icc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hE t ht).hasDerivWithinAt) (C := 0) (fun _ _ => by simp)
    (show 0 ∈ Icc 0 s from ⟨le_rfl, hs⟩) (show s ∈ Icc 0 s from ⟨hs, le_rfl⟩)
  have heq : E s = E 0 := by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using H
  simpa only [E, z, q, stableRescaledFlow_initial, stableRescaledDifferential_initial,
    ContinuousLinearMap.id_apply] using heq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_fderiv_weak {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40) (hu : y 1 = 0)
    (hw : |y 2| < 1 / 200) (v : StableState) :
    (stableBoundaryProjection (y 0) (y 1) (y 2) + 1) *
      fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v =
        (y 0 + 1) * v 0 + y 2 * (v 2 - 2 * v 1) := by
  let z := stableRescaledFlow (c + 1) y
  let q := fun t => stableRescaledDifferential (c + 1) y t v
  let P := stableBoundaryProjection (y 0) (y 1) (y 2)
  have hu' : |y 1| < 1 / 200 := by rw [hu]; norm_num
  have hz := tendsto_pi_nhds.mp (stableRescaledFlow_limit (by linarith : 0 < c + 1) hc hm.le hu'.le hw.le)
  have hq : Tendsto (fun t => q t 0) atTop
      (𝓝 (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v)) := by
    rw [stableBoundaryProjection_fderiv_eq hc hm hu' hw]
    exact (continuousAt_id.clm_apply continuousAt_const).tendsto.comp
      (stableCenterDifferential_tendsto hc hm.le hu'.le hw.le)
  have hbounded (i : Fin 3) : IsBoundedUnder (· ≤ ·) atTop (fun t => ‖q t i‖) := by
    refine ⟨Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖, ?_⟩
    change ∀ᶠ t in atTop, ‖q t i‖ ≤ _
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (norm_le_pi_norm (q t) i).trans (stableRescaledDifferential_bound hc hm.le hu'.le hw.le ht v)
  have hW : Tendsto (fun t => z t 2) atTop (𝓝 0) := hz 2
  have hWq (i : Fin 3) : Tendsto (fun t => z t 2 * q t i) atTop (𝓝 0) :=
    hW.zero_mul_isBoundedUnder_le (hbounded i)
  have hlim := (((hz 0).add_const 1).mul hq).add ((hWq 2).sub ((hWq 1).const_mul 2))
  have heq : (fun t => (z t 0 + 1) * q t 0 + (z t 2 * q t 2 - 2 * (z t 2 * q t 1))) =ᶠ[atTop]
      (fun _ => (y 0 + 1) * v 0 + y 2 * (v 2 - 2 * v 1)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have H := stableRescaledDifferential_weak_energy (v := v) hc hm.le hu hw.le ht
    dsimp only at H
    change (z t 0 + 1) * q t 0 + z t 2 * (q t 2 - 2 * q t 1) = _ at H
    nlinarith only [H]
  have H := tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds
  simpa only [Matrix.cons_val_zero, sub_self, mul_zero, zero_sub, add_zero] using H

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

private theorem BianchiIX.contDiffAt_entranceStablePhase_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 2 entranceStablePhase y :=
  (contDiffAt_stableBoundaryProjection_two (y := stableRestriction y) hm hu hw).comp y
    stableRestriction.contDiff.contDiffAt

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
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_compactConnectionEntry_two {η : ℝ} {Y : CoreAngleState}
    (h : ContDiffAt ℝ 2 (coreTailState η) Y) :
    ContDiffAt ℝ 2 (compactConnectionEntry η) Y := by
  have hr : ContDiff ℝ 2 projectiveReflection := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [projectiveReflection] <;> fun_prop
  exact hr.contDiffAt.comp Y h

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.compactConnection_reference_stable_phase {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    2 < compactConnectionEntry η ![k, 0, 0] 0 ∧
      entranceStablePhase (compactConnectionEntry η ![k, 0, 0]) = k - 1 := by
  have hk0 : 0 ≤ k := by linarith
  have hk2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) hk 2
  have hη2 := pow_le_pow_left₀ hη.1.le hη.2 2
  have hsq : 0 ≤ k ^ 2 - η ^ 2 := by nlinarith only [hk2, hη2]
  have hs := Real.sq_sqrt hsq
  have hm : 2 < Real.sqrt (k ^ 2 - η ^ 2) - 1 := by
    nlinarith only [hs, Real.sqrt_nonneg (k ^ 2 - η ^ 2), hk2, hη2]
  have heq : compactConnectionEntry η ![k, 0, 0] = ![Real.sqrt (k ^ 2 - η ^ 2) - 1, 0, 0, η] :=
    coreTail_reflected_reference (by linarith) ⟨hη.1, by linarith [hη.2]⟩
  rw [heq]
  refine ⟨hm, ?_⟩
  change stableBoundaryProjection (Real.sqrt (k ^ 2 - η ^ 2) - 1) 0 η = k - 1
  rw [stableBoundaryProjection_weak hm.le (by simp) (by rw [abs_of_pos hη.1]; linarith [hη.2])]
  unfold stableWeakRadius phaseNorm
  rw [show (Real.sqrt (k ^ 2 - η ^ 2) - 1 + 1) ^ 2 + η ^ 2 = k ^ 2 by nlinarith only [hs],
    Real.sqrt_sq hk0]

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.compactConnectionFinitePhase_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    compactConnectionFinitePhase η ![k, 0, 0] = k - 2 := by
  have hP := (compactConnection_reference_stable_phase hk hη).2
  have hv : compactConnectionEntry η ![k, 0, 0] 2 = 0 := by
    change projectiveReflection (coreTailState η ![k, 0, 0]) 2 = 0
    rw [coreTail_reflected_reference (by linarith) ⟨hη.1, by linarith [hη.2]⟩]
    rfl
  unfold compactConnectionFinitePhase entranceStableRadius
  rw [hP, hv]
  change Real.sqrt ((k - 1 - 1) ^ 2 + 0 ^ 2) = k - 2
  rw [show (k - 1 - 1) ^ 2 + 0 ^ 2 = (k - 2) ^ 2 by ring,
    Real.sqrt_sq (by linarith)]

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_compactConnectionFinitePhase_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ContDiffAt ℝ 2 (compactConnectionFinitePhase η) ![k, 0, 0] := by
  let Y : CoreAngleState := ![k, 0, 0]
  let y := compactConnectionEntry η Y
  have H := coreTail_reference_regular (by linarith : 1 < k) ⟨hη.1, by linarith [hη.2]⟩
  have hentry : ContDiffAt ℝ 2 (compactConnectionEntry η) Y := contDiffAt_compactConnectionEntry_two H.2.2.2.1
  have hdata := compactConnection_reference_stable_phase hk hη
  have heq : y = ![Real.sqrt (k ^ 2 - η ^ 2) - 1, 0, 0, η] :=
    coreTail_reflected_reference (by linarith) ⟨hη.1, by linarith [hη.2]⟩
  have hP : ContDiffAt ℝ 2 entranceStablePhase y := contDiffAt_entranceStablePhase_two hdata.1.le
    (by rw [heq]; norm_num) (by rw [heq]; change |η| < 1 / 200; rw [abs_of_pos hη.1]; linarith [hη.2])
  have hn : (entranceStablePhase y - 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have hp : 0 < entranceStablePhase y - 1 := by change 0 < entranceStablePhase (compactConnectionEntry η Y) - 1; rw [hdata.2]; linarith
    positivity
  have hR : ContDiffAt ℝ 2 entranceStableRadius y :=
    (((hP.sub contDiffAt_const).pow 2).add ((by fun_prop : ContDiffAt ℝ 2 (fun z : ProjectiveState => z 2) y).pow 2)).sqrt hn
  exact hR.comp Y hentry

end
end

/-- The strong boundary response in (B.48) is independent of the auxiliary tail height. -/
theorem solution {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    fderiv ℝ (compactConnectionFinitePhase η) ![k, 0, 0] (Pi.single 1 1) = -2 / k := by
  let Y : CoreAngleState := ![k, 0, 0]
  let c := fun a : ℝ => (![k, a, 0] : CoreAngleState)
  let Z := coreTailState η Y
  let v := fderiv ℝ (coreTailState η) Y (Pi.single 1 1)
  let y : StableState := ![-Z 0, Z 1, Z 2]
  let w : StableState := ![-v 0, v 1, v 2]
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  let q := fderiv ℝ P y w
  let d := fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single 1 1)
  have hk1 : 1 < k := by linarith
  have hη1 : 0 < η ∧ η < 1 := ⟨hη.1, by linarith [hη.2]⟩
  have HT := coreTail_reference_regular hk1 hη1
  have hZ : Z = ![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] := HT.2.1
  have hm : 2 ≤ y 0 := (compactConnection_reference_stable_phase hk hη).1.le
  have hu : y 1 = 0 := by change Z 1 = 0; rw [hZ]; rfl
  have hw : |y 2| < 1 / 200 := by
    change |Z 2| < 1 / 200
    rw [hZ]
    change |η| < 1 / 200
    rw [abs_of_pos hη.1]
    linarith [hη.2]
  have hPval : entranceStablePhase (compactConnectionEntry η Y) = k - 1 :=
    (compactConnection_reference_stable_phase hk hη).2
  have hFval : compactConnectionFinitePhase η Y = k - 2 := compactConnectionFinitePhase_reference hk hη
  have hlinear := stableBoundaryProjection_fderiv_weak hm (by simp : |y 0 - y 0| < (1 : ℝ) / 40) hu hw w
  change (entranceStablePhase (compactConnectionEntry η Y) + 1) * q =
    (-Z 0 + 1) * (-v 0) + Z 2 * (v 2 - 2 * v 1) at hlinear
  rw [hPval] at hlinear
  have HI := coreTail_strong_variation_invariant hk1 hη1
  change (Z 0 - 1) * v 0 + Z 2 * v 2 - 2 * Z 2 * v 1 = -2 at HI
  have hq : k * q = -2 := by nlinarith only [hlinear, HI]
  have hline : HasDerivAt c (Pi.single 1 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c] using hasDerivAt_const (0 : ℝ) k
    · change HasDerivAt (fun a : ℝ => a) 1 0
      exact hasDerivAt_id' 0
    · simpa [c] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have htD : HasFDerivAt (coreTailState η) (fderiv ℝ (coreTailState η) Y) Y :=
    (HT.2.2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  have htail : HasDerivAt (fun a => coreTailState η (c a)) v 0 := by
    have H := htD.comp_hasDerivAt (0 : ℝ) hline
    exact H
  have hstable : HasDerivAt (fun a => (![-coreTailState η (c a) 0,
      coreTailState η (c a) 1, coreTailState η (c a) 2] : StableState)) w 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hasDerivAt_pi.mp htail 0).neg
    · exact hasDerivAt_pi.mp htail 1
    · exact hasDerivAt_pi.mp htail 2
  have hpD : HasFDerivAt P (fderiv ℝ P y) y :=
    ((contDiffAt_stableBoundaryProjection_two hm (by rw [hu]; norm_num) hw).differentiableAt (by norm_num)).hasFDerivAt
  have hP : HasDerivAt (fun a => entranceStablePhase (compactConnectionEntry η (c a))) q 0 := by
    have H := hpD.comp_hasDerivAt (0 : ℝ) hstable
    exact H
  have hfD : HasFDerivAt (compactConnectionFinitePhase η) (fderiv ℝ (compactConnectionFinitePhase η) Y) Y :=
    ((contDiffAt_compactConnectionFinitePhase_reference hk hη).differentiableAt (by norm_num)).hasFDerivAt
  have hF : HasDerivAt (fun a => compactConnectionFinitePhase η (c a)) d 0 := by
    have H := hfD.comp_hasDerivAt (0 : ℝ) hline
    exact H
  have hV : HasDerivAt (fun a => compactConnectionEntry η (c a) 2) (v 3) 0 := hasDerivAt_pi.mp htail 3
  have heq : (fun a => compactConnectionFinitePhase η (c a) ^ 2) =ᶠ[𝓝 0]
      (fun a => (entranceStablePhase (compactConnectionEntry η (c a)) - 1) ^ 2 +
        compactConnectionEntry η (c a) 2 ^ 2) :=
    Eventually.of_forall (fun a => entranceStableRadius_sq (compactConnectionEntry η (c a)))
  have HE := ((hF.pow 2).congr_of_eventuallyEq heq.symm).unique (((hP.sub_const 1).pow 2).add (hV.pow 2))
  change 2 * (compactConnectionFinitePhase η Y) ^ (2 - 1) * d =
    2 * (entranceStablePhase (compactConnectionEntry η Y) - 1) ^ (2 - 1) * q +
      2 * (Z 3) ^ (2 - 1) * v 3 at HE
  rw [hFval, hPval, hZ] at HE
  change 2 * (k - 2) ^ (2 - 1) * d = 2 * (k - 1 - 1) ^ (2 - 1) * q +
    2 * (0 : ℝ) ^ (2 - 1) * v 3 at HE
  norm_num at HE
  have hpos : 0 < 2 * (k - 2) := by linarith
  have hdq : d = q := mul_left_cancel₀ hpos.ne' (by nlinarith only [HE])
  change d = -2 / k
  rw [hdq]
  apply (eq_div_iff (by linarith : k ≠ 0)).mpr
  linarith only [hq]
