-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_phase_expansion
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:31:01.204425+00:00
-- url     : https://prove2.me/submissions/297279fa-5575-4807-8006-4a8e874463e3

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Theorems.Thm_BianchiIX_compactConnectionFinitePhase_strong_reference
import Theorems.Thm_BianchiIX_contDiffAt_coreTailMultiplier_two
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_moving_intervalIntegral_two
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_normalizedProjectiveWallMultiplier_two
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_coreTailMultiplier_formula
import Theorems.Thm_BianchiIX_coreTailState_wall_zero
import Theorems.Thm_BianchiIX_coreTail_reference_regular
import Theorems.Thm_BianchiIX_coreTail_weak_energy_factorization
import Theorems.Thm_BianchiIX_exists_compact_connection_finite_phase_bounds
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_stable_global_region
import Theorems.Thm_BianchiIX_normalized_stable_limit
import Theorems.Thm_BianchiIX_stableResidualIntegral_bound
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
open Set

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
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreTailEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreTailEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreTailEntry] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailState_active {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    coreTailState η Y 2 = η := hvalid.1.1.2.2

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
open Set

private theorem BianchiIX.coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_coreTailWeakEnergyIntegrand_two {η t : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (H : coreTailValid η Y) (ht : t ∈ Icc 0 (coreTailTime η Y)) :
    ContDiffAt ℝ 2 coreTailWeakEnergyIntegrand (Y, t) := by
  let c := fun Z => fromProjectiveState (coreTailEntry Z)
  have hD := coreTailValid_denom_pos H
  have hc : ContDiffAt ℝ 2 c Y :=
    (contDiffAt_fromProjectiveState 2 hD.ne').comp Y (contDiffAt_coreTailEntry 2 hk)
  have hp : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => (c p.1, p.2)) (Y, t) :=
    (hc.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hn := (contDiffAt_normalizedMaxCurve_two (H.2.1 t ht).1).comp (Y, t)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (f := fun p : CoreAngleState × ℝ => (c p.1, p.2)) hp
  have ha : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => normalizedProjectiveRate (c p.1) 0 p.2) (Y, t) :=
    contDiffAt_const.add (contDiffAt_pi.mp hn 0)
  have hy : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreTailEntry p.1) 0 p.2) (Y, t) :=
    (contDiffAt_toProjectiveState 2 (H.2.1 t ht).2.ne').comp (Y, t)
      (g := toProjectiveState) (f := fun p : CoreAngleState × ℝ => normalizedMaxCurve (c p.1) 0 p.2) hn
  have hb : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => normalizedProjectiveWallMultiplier (c p.1) p.2 2) (Y, t) :=
    (contDiffAt_normalizedProjectiveWallMultiplier_two
    (c := fun p : CoreAngleState × ℝ => c p.1) (τ := fun p => p.2) (Y := (Y, t))
    (hc.comp (Y, t) contDiffAt_fst) contDiffAt_snd ht.1
    (fun s hs => (H.2.1 s ⟨hs.1, hs.2.trans ht.2⟩).1)
    (fromProjectiveState_clock_pos hD) (H.2.1 t ht).2 2).1
  exact ((contDiffAt_const.mul ha).mul ((contDiffAt_pi.mp hy 0).sub contDiffAt_const)).mul (hb.pow 2)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_coreTailWeakEnergyCoefficient_two {η : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (H : coreTailValid η Y) (hT : ContDiffAt ℝ 2 (coreTailTime η) Y) :
    ContDiffAt ℝ 2 (coreTailWeakEnergyCoefficient η) Y :=
  contDiffAt_moving_intervalIntegral_two hT H.1.1.1.le
    (fun _ ht => contDiffAt_coreTailWeakEnergyIntegrand_two hk H ht)

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
open Filter
open scoped Topology

private theorem BianchiIX.entranceStablePhase_weak {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : y 1 = 0) (hw : |y 3| ≤ 1 / 200) :
    entranceStablePhase y = stableWeakRadius (y 0) (y 3) - 1 := by
  unfold entranceStablePhase
  rw [hu]
  exact stableBoundaryProjection_weak hm (by simp) hw

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

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.compactConnectionFinitePhase_weak {η : ℝ} {Y : CoreAngleState}
    (hη : |η| ≤ 1 / 200) (htail : coreTailValid η Y)
    (hm : 2 ≤ -coreTailState η Y 0) (hu : Y 1 = 0) :
    compactConnectionFinitePhase η Y =
      phaseNorm (coreRadius (coreTailState η Y 0) η - 2) (coreTailState η Y 3) := by
  have hU : compactConnectionEntry η Y 1 = 0 := coreTailState_wall_zero htail 0 hu
  have hW : compactConnectionEntry η Y 3 = η := coreTailState_active htail
  have hP := entranceStablePhase_weak hm hU (by rw [hW]; exact hη)
  unfold compactConnectionFinitePhase entranceStableRadius
  rw [hP, hW]
  have hs : stableWeakRadius (compactConnectionEntry η Y 0) η = coreRadius (coreTailState η Y 0) η := by
    change Real.sqrt ((-coreTailState η Y 0 + 1) ^ 2 + η ^ 2) =
      Real.sqrt ((coreTailState η Y 0 - 1) ^ 2 + η ^ 2)
    congr 1
    ring
  rw [hs]
  change Real.sqrt ((coreRadius (coreTailState η Y 0) η - 1 - 1) ^ 2 + (coreTailState η Y 3) ^ 2) = _
  unfold phaseNorm
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.compactConnectionFinitePhase_radial_reference {k η : ℝ}
    (hk : 31 / 8 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    fderiv ℝ (compactConnectionFinitePhase η) ![k, 0, 0] (Pi.single 0 1) = 1 := by
  have hline : HasDerivAt (fun a : ℝ => (![a, 0, 0] : CoreAngleState)) (Pi.single 0 1) k := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt (fun a : ℝ => a) 1 k
      exact hasDerivAt_id' k
    · simpa using hasDerivAt_const k (0 : ℝ)
    · simpa using hasDerivAt_const k (0 : ℝ)
  have hF := (contDiffAt_compactConnectionFinitePhase_reference (k := k) (by linarith only [hk]) hη).differentiableAt (by norm_num)
  have H := hF.hasFDerivAt.comp_hasDerivAt k hline
  have heq : (fun a : ℝ => compactConnectionFinitePhase η ![a, 0, 0]) =ᶠ[𝓝 k] (fun a => a - 2) := by
    filter_upwards [eventually_gt_nhds (show 7 / 2 < k by linarith)] with a ha
    exact compactConnectionFinitePhase_reference ha.le hη
  exact (H.congr_of_eventuallyEq heq.symm).unique ((hasDerivAt_id' k).sub_const 2)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.compactConnectionFinitePhase_weak_factorization {η : ℝ} {Y : CoreAngleState}
    (hk : 2 < Y 0) (hη : |η| ≤ 1 / 200) (H : coreTailValid η Y)
    (hm : 2 ≤ -coreTailState η Y 0) (hu : Y 1 = 0) :
    compactConnectionFinitePhase η Y = Y 0 - 2 + (Y 2) ^ 2 * compactConnectionWeakCoefficient η Y := by
  let F := compactConnectionFinitePhase η Y
  let R := coreRadius (coreTailState η Y 0) η
  let I := coreTailWeakEnergyCoefficient η Y
  let B := coreTailMultiplier η Y 1
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hdR : R + Y 0 ≠ 0 := by linarith only [hR0, hk]
  have hdF : F + Y 0 - 2 ≠ 0 := by linarith only [hF0, hk]
  have hE : R ^ 2 = (Y 0) ^ 2 + (Y 2) ^ 2 * I := coreTail_weak_energy_factorization (by linarith) H hu
  have hW : coreTailState η Y 3 = Y 2 * B := coreTailMultiplier_formula H 1
  have hF2 : F ^ 2 = (R - 2) ^ 2 + (Y 2 * B) ^ 2 := by
    dsimp only [F]
    rw [compactConnectionFinitePhase_weak hη H hm hu, phaseNorm_sq, hW]
  have hRdiff : R - Y 0 = (Y 2) ^ 2 * I / (R + Y 0) := by
    apply (eq_div_iff hdR).mpr
    nlinarith only [hE]
  have hprod : (F - (Y 0 - 2)) * (F + Y 0 - 2) =
      (Y 2) ^ 2 * (I * (1 - 4 / (R + Y 0)) + B ^ 2) := by
    calc
      _ = (R ^ 2 - (Y 0) ^ 2) - 4 * (R - Y 0) + (Y 2 * B) ^ 2 := by nlinarith only [hF2]
      _ = _ := by rw [hE, hRdiff]; ring
  have hdiff : F - (Y 0 - 2) = (Y 2) ^ 2 *
      ((I * (1 - 4 / (R + Y 0)) + B ^ 2) / (F + Y 0 - 2)) := by
    rw [← mul_div_assoc]
    exact (eq_div_iff hdF).mpr hprod
  change F = Y 0 - 2 + (Y 2) ^ 2 * ((I * (1 - 4 / (R + Y 0)) + B ^ 2) / (F + Y 0 - 2))
  linarith only [hdiff]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_compactConnectionWeakCoefficient_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ContDiffAt ℝ 2 (compactConnectionWeakCoefficient η) ![k, 0, 0] := by
  let Y : CoreAngleState := ![k, 0, 0]
  have hk1 : 1 < k := by linarith
  have H := coreTail_reference_regular hk1 ⟨hη.1, by linarith [hη.2]⟩
  have htail : coreTailValid η Y := H.2.2.2.2.self_of_nhds
  have hI := contDiffAt_coreTailWeakEnergyCoefficient_two hk1 htail H.2.2.1
  have hB := (contDiffAt_coreTailMultiplier_two hk1 htail H.2.2.1 1).1
  have hF := contDiffAt_compactConnectionFinitePhase_reference hk hη
  have hR : ContDiffAt ℝ 2 (fun Z => coreRadius (coreTailState η Z 0) η) Y := by
    have hM := contDiffAt_pi.mp H.2.2.2.1 0
    exact (((hM.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt (by positivity [hη.1])
  have hK : ContDiffAt ℝ 2 (fun Z : CoreAngleState => Z 0) Y := by fun_prop
  have hdR : coreRadius (coreTailState η Y 0) η + Y 0 ≠ 0 := by
    have hR0 : 0 ≤ coreRadius (coreTailState η Y 0) η := Real.sqrt_nonneg _
    change coreRadius (coreTailState η Y 0) η + k ≠ 0
    linarith only [hk, hR0]
  have hdF : compactConnectionFinitePhase η Y + Y 0 - 2 ≠ 0 := by
    rw [compactConnectionFinitePhase_reference hk hη]
    change k - 2 + k - 2 ≠ 0
    linarith only [hk]
  exact ((hI.mul (contDiffAt_const.sub (contDiffAt_const.div (hR.add hK) hdR))).add (hB.pow 2)).div
    ((hF.add hK).sub contDiffAt_const) hdF

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.compactConnectionFinitePhase_weak_germ {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    (fun p : ℝ × ℝ => compactConnectionFinitePhase η ![p.1, 0, p.2]) =ᶠ[𝓝 (k, 0)]
      (fun p => p.1 - 2 + p.2 ^ 2 * compactConnectionWeakCoefficient η ![p.1, 0, p.2]) := by
  let c := fun p : ℝ × ℝ => (![p.1, 0, p.2] : CoreAngleState)
  have hc : Tendsto c (𝓝 (k, 0)) (𝓝 (![k, 0, 0] : CoreAngleState)) :=
    (by fun_prop : Continuous c).continuousAt.tendsto
  have H := coreTail_reference_regular (by linarith : 1 < k) ⟨hη.1, by linarith [hη.2]⟩
  have hm0 : 2 < -coreTailState η ![k, 0, 0] 0 := (compactConnection_reference_stable_phase hk hη).1
  have hm := ((contDiffAt_pi.mp H.2.2.2.1 0).neg.continuousAt).eventually (eventually_gt_nhds hm0)
  have hkp : ∀ᶠ p : ℝ × ℝ in 𝓝 (k, 0), 2 < p.1 :=
    continuousAt_fst.eventually (eventually_gt_nhds (show 2 < k by linarith))
  filter_upwards [hc.eventually H.2.2.2.2, hc.eventually hm, hkp] with p hp hm' hk'
  exact compactConnectionFinitePhase_weak_factorization hk'
    (by rw [abs_of_pos hη.1]; linarith [hη.2]) hp hm'.le rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.compactConnectionFinitePhase_weak_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    fderiv ℝ (compactConnectionFinitePhase η) ![k, 0, 0] (Pi.single 2 1) = 0 := by
  have hline : HasDerivAt (fun w : ℝ => (![k, 0, w] : CoreAngleState)) (Pi.single 2 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_const (0 : ℝ) k
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · change HasDerivAt (fun w : ℝ => w) 1 0
      exact hasDerivAt_id' 0
  have hQ := ((contDiffAt_compactConnectionWeakCoefficient_reference hk hη).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hF := ((contDiffAt_compactConnectionFinitePhase_reference hk hη).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hd : HasDerivAt (fun w : ℝ => k - 2 + w ^ 2 * compactConnectionWeakCoefficient η ![k, 0, w]) 0 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (k - 2)).add (((hasDerivAt_id' (0 : ℝ)).pow 2).mul hQ) using 1
    simp
  have heq : (fun w : ℝ => compactConnectionFinitePhase η ![k, 0, w]) =ᶠ[𝓝 0]
      (fun w => k - 2 + w ^ 2 * compactConnectionWeakCoefficient η ![k, 0, w]) :=
    (by fun_prop : Continuous (fun w : ℝ => (k, w))).continuousAt.tendsto.eventually
      (compactConnectionFinitePhase_weak_germ hk hη)
  exact (hF.congr_of_eventuallyEq heq.symm).unique hd

end
end

/-- Both parts of (B.48), with a common signed neighborhood and uniform constants. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y ∧
        |compactConnectionFinitePhase η Y - (Y 0 - 2 - 2 * Y 1 / Y 0)| ≤
          C * (|Y 1| + |Y 2|) ^ 2 ∧
        ∀ i : Fin 3, |fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single i 1) -
          (![1, -2 / Y 0, 0] : Fin 3 → ℝ) i| ≤ C * (|Y 1| + |Y 2|) := by
  obtain ⟨ε, hε, C, hC, HC⟩ := exists_compact_connection_finite_phase_bounds hη
  let F := compactConnectionFinitePhase η
  let S : Set CoreAngleState := Icc (![31 / 8, -ε, -ε] : CoreAngleState) ![6, ε, ε]
  have hcoords {Y : CoreAngleState} (hY : Y ∈ S) :
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) ∧ |Y 1| ≤ ε ∧ |Y 2| ≤ ε :=
    ⟨⟨hY.1 0, hY.2 0⟩, abs_le.mpr ⟨hY.1 1, hY.2 1⟩, abs_le.mpr ⟨hY.1 2, hY.2 2⟩⟩
  have hmem {Y : CoreAngleState} (hk : 31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6)
      (hu : |Y 1| ≤ ε) (hw : |Y 2| ≤ ε) : Y ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hk.1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · intro i
      fin_cases i
      · exact hk.2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have hreg (Y : CoreAngleState) (hY : Y ∈ S) :=
    HC Y (hcoords hY).1 (hcoords hY).2.1 (hcoords hY).2.2
  have hdiff (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ (fderiv ℝ F) Y :=
    (((hreg Y hY).2.1).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hbound (Y : CoreAngleState) (hY : Y ∈ S) : ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ C := by
    have H := (hreg Y hY).2.2
    change |F Y| + ‖fderiv ℝ F Y‖ + ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ C at H
    linarith only [H, abs_nonneg (F Y), norm_nonneg (fderiv ℝ F Y)]
  have hLip {X Z : CoreAngleState} (hX : X ∈ S) (hZ : Z ∈ S) :
      ‖fderiv ℝ F X - fderiv ℝ F Z‖ ≤ C * ‖X - Z‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_Icc _ _) hZ hX
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  let Z : CoreAngleState := ![Y 0, 0, 0]
  let b := |Y 1| + |Y 2|
  have hb : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hY : Y ∈ S := hmem hk hu hw
  have hZ : Z ∈ S := hmem hk (by simpa [Z] using hε.le) (by simpa [Z] using hε.le)
  have hdist : ‖Y - Z‖ ≤ b := by
    apply (pi_norm_le_iff_of_nonneg hb).mpr
    intro i
    fin_cases i
    · change |Y 0 - Y 0| ≤ b
      simpa only [sub_self, abs_zero] using hb
    · change |Y 1 - 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_zero] using le_add_of_nonneg_right (abs_nonneg (Y 2))
    · change |Y 2 - 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_zero] using le_add_of_nonneg_left (abs_nonneg (Y 1))
  have hk' : 7 / 2 ≤ Y 0 := by linarith only [hk.1]
  have haxis (i : Fin 3) : fderiv ℝ F Z (Pi.single i 1) = (![1, -2 / Y 0, 0] : Fin 3 → ℝ) i := by
    fin_cases i
    · exact compactConnectionFinitePhase_radial_reference hk.1 hη
    · exact compactConnectionFinitePhase_strong_reference hk' hη
    · exact compactConnectionFinitePhase_weak_reference hk' hη
  have hvalue : F Z = Y 0 - 2 := compactConnectionFinitePhase_reference hk' hη
  have hlin : fderiv ℝ F Z (Y - Z) = -2 * Y 1 / Y 0 := by
    have hv : Y - Z = Y 1 • Pi.single 1 1 + Y 2 • Pi.single 2 1 := by
      ext i
      fin_cases i <;> simp [Z]
    rw [hv, map_add, map_smul, map_smul, haxis 1, haxis 2]
    change Y 1 * (-2 / Y 0) + Y 2 * 0 = _
    ring
  have hrem : |F Y - F Z - fderiv ℝ F Z (Y - Z)| ≤ C * ‖Y - Z‖ ^ 2 := by
    let g := fun X : CoreAngleState => F X - fderiv ℝ F Z X
    have hseg {X : CoreAngleState} (hX : X ∈ segment ℝ Z Y) : X ∈ S :=
      (convex_Icc _ _).segment_subset hZ hY hX
    have hg (X : CoreAngleState) (hX : X ∈ segment ℝ Z Y) :
        HasFDerivAt g (fderiv ℝ F X - fderiv ℝ F Z) X :=
      (((hreg X (hseg hX)).2.1).differentiableAt (by norm_num)).hasFDerivAt.sub (fderiv ℝ F Z).hasFDerivAt
    have hbg (X : CoreAngleState) (hX : X ∈ segment ℝ Z Y) :
        ‖fderiv ℝ F X - fderiv ℝ F Z‖ ≤ C * ‖Y - Z‖ :=
      (hLip (hseg hX) hZ).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hX) hC.le)
    have H := (convex_segment Z Y).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun X hX => (hg X hX).hasFDerivWithinAt) hbg (left_mem_segment ℝ Z Y) (right_mem_segment ℝ Z Y)
    simpa only [g, map_sub, sub_sub_sub_comm, Real.norm_eq_abs, pow_two, mul_assoc] using H
  refine ⟨(hreg Y hY).1, (hreg Y hY).2.1, ?_, ?_⟩
  · change |F Y - (Y 0 - 2 - 2 * Y 1 / Y 0)| ≤ C * b ^ 2
    calc
      _ = |F Y - F Z - fderiv ℝ F Z (Y - Z)| := by rw [hvalue, hlin]; congr 1; ring
      _ ≤ C * ‖Y - Z‖ ^ 2 := hrem
      _ ≤ C * b ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist 2) hC.le
  · intro i
    rw [← haxis i]
    have H := (fderiv ℝ F Y - fderiv ℝ F Z).le_opNorm (Pi.single i 1)
    have H' : |fderiv ℝ F Y (Pi.single i 1) - fderiv ℝ F Z (Pi.single i 1)| ≤
        ‖fderiv ℝ F Y - fderiv ℝ F Z‖ := by
      simpa only [sub_apply, Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using H
    exact H'.trans ((hLip hY hZ).trans (mul_le_mul_of_nonneg_left hdist hC.le))
