-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_coordinate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:27:35.320522+00:00
-- url     : https://prove2.me/submissions/341addbe-8879-4aaa-b460-17209fc1817e

import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_contDiffAt_coreTailMultiplier_two
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_coreTail_reference_regular
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
open Set Filter Metric
open scoped Topology

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
open Set MeasureTheory

private theorem BianchiIX.normalizedProjectiveWallMultiplier_pos (x : NormalizedState) (T : ℝ) (i : Fin 3) :
    0 < normalizedProjectiveWallMultiplier x T i := Real.exp_pos _

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

private theorem BianchiIX.coreTailMultiplier_pos (η : ℝ) (Y : CoreAngleState) (i : Fin 2) :
    0 < coreTailMultiplier η Y i := normalizedProjectiveWallMultiplier_pos _ _ _

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

/-- Actual coordinate identities hold on neighborhoods, including the ends of the compact interval. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ A : ℝ, 1 ≤ A ∧ ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      (∀ᶠ Z in 𝓝 Y, coreTailValid η Z) ∧ ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y ∧
        ‖fderiv ℝ (compactConnectionFinitePhase η) Y‖ ≤ A ∧
        ∀ i : Fin 2, ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
          0 < coreTailMultiplier η Y i ∧ coreTailMultiplier η Y i ≤ A ∧
          ‖fderiv ℝ (fun Z => coreTailMultiplier η Z i) Y‖ ≤ A := by
  let F := compactConnectionFinitePhase η
  let B := coreTailMultiplier η
  let G : Set CoreAngleState := {Y | 1 < Y 0 ∧ coreTailValid η Y ∧
    ContDiffAt ℝ 2 (coreTailTime η) Y ∧ ContDiffAt ℝ 2 F Y}
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc (31 / 8) 6
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    have hk1 : 1 < k := by linarith only [hk.1]
    have H := coreTail_reference_regular hk1 ⟨hη.1, by linarith [hη.2]⟩
    have hcoord : ∀ᶠ Y : CoreAngleState in 𝓝 ![k, 0, 0], 1 < Y 0 :=
      ((continuous_apply 0).continuousAt : ContinuousAt (fun Y : CoreAngleState => Y 0) ![k, 0, 0]).eventually (lt_mem_nhds hk1)
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hcoord, H.2.2.2.2, H.2.2.1.eventually (by norm_num),
      (contDiffAt_compactConnectionFinitePhase_reference (by linarith only [hk.1]) hη).eventually (by norm_num)]
      with Z hkZ hv ht hf
    exact ⟨hkZ, hv, ht, hf⟩
  obtain ⟨ε, hε, hεG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening ε S
  have hWG : W ⊆ G := hεG.trans interior_subset
  have hreg (Y : CoreAngleState) (hY : Y ∈ W) (i : Fin 2) :
      ContDiffAt ℝ 2 (fun Z => B Z i) Y :=
    (contDiffAt_coreTailMultiplier_two (hWG hY).1 (hWG hY).2.1 (hWG hY).2.2.1 i).1
  let q := fun Y => ‖fderiv ℝ F Y‖ +
    (B Y 0 + ‖fderiv ℝ (fun Z => B Z 0) Y‖) + (B Y 1 + ‖fderiv ℝ (fun Z => B Z 1) Y‖)
  have hq : ContinuousOn q W := by
    intro Y hY
    have hF := (hWG hY).2.2.2
    have hb (i : Fin 2) := (hreg Y hY i).continuousAt.add
      ((hreg Y hY i).continuousAt_fderiv (by norm_num)).norm
    exact (((hF.continuousAt_fderiv (by norm_num)).norm.add (hb 0)).add (hb 1)).continuousWithinAt
  obtain ⟨C, hC⟩ := hS.cthickening.exists_bound_of_continuousOn hq
  refine ⟨ε, hε, max C 1, le_max_right _ _, ?_⟩
  intro Y hk hu hw
  have hd : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ε := by
    apply (dist_pi_le_iff hε.le).mpr
    intro i
    fin_cases i
    · simpa using hε.le
    · simpa [Real.dist_eq] using hu
    · simpa [Real.dist_eq] using hw
  have hY : Y ∈ W := mem_cthickening_of_dist_le Y _ ε S ⟨Y 0, hk, rfl⟩ hd
  have hloc : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z := by
    have H : ∀ᶠ Z in 𝓝 Y, Z ∈ G := mem_interior_iff_mem_nhds.mp (hεG hY)
    exact H.mono (fun _ hz => hz.2.1)
  have Hb : q Y ≤ max C 1 := (le_abs_self _).trans ((hC Y hY).trans (le_max_left _ _))
  have hp0 : 0 ≤ B Y 0 := (coreTailMultiplier_pos η Y 0).le
  have hp1 : 0 ≤ B Y 1 := (coreTailMultiplier_pos η Y 1).le
  dsimp only [q] at Hb
  refine ⟨hloc, (hWG hY).2.2.2, ?_, ?_⟩
  · linarith only [Hb, hp0, hp1, norm_nonneg (fderiv ℝ (fun Z => B Z 0) Y), norm_nonneg (fderiv ℝ (fun Z => B Z 1) Y)]
  · intro i
    have H0 : B Y 0 ≤ max C 1 ∧ ‖fderiv ℝ (fun Z => B Z 0) Y‖ ≤ max C 1 := by
      constructor <;> linarith only [Hb, hp0, hp1, norm_nonneg (fderiv ℝ F Y),
        norm_nonneg (fderiv ℝ (fun Z => B Z 0) Y), norm_nonneg (fderiv ℝ (fun Z => B Z 1) Y)]
    have H1 : B Y 1 ≤ max C 1 ∧ ‖fderiv ℝ (fun Z => B Z 1) Y‖ ≤ max C 1 := by
      constructor <;> linarith only [Hb, hp0, hp1, norm_nonneg (fderiv ℝ F Y),
        norm_nonneg (fderiv ℝ (fun Z => B Z 0) Y), norm_nonneg (fderiv ℝ (fun Z => B Z 1) Y)]
    refine ⟨hreg Y hY i, coreTailMultiplier_pos η Y i, ?_⟩
    fin_cases i
    · exact H0
    · exact H1
