-- Prove2me | solution 1 for BianchiIX.stableResidualIntegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:16:46.191651+00:00
-- url     : https://prove2.me/submissions/c25ed0f7-37d4-45dd-97a3-aa346871318a

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_integral_clock_exp_decay
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_stable_global_region
import Theorems.Thm_BianchiIX_scaled_stable_boundary_drift
import Theorems.Thm_BianchiIX_stableResidual_coefficients_bound
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

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
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

private theorem BianchiIX.stableCorrectedResidual_bound {m u w : ℝ} (hm : 3 / 2 ≤ m) :
    |stableCorrectedResidual m u w| ≤ 64 / (m + 1) * |u| * (|u| + |w|) ^ 3 := by
  obtain ⟨h4, h3, h2, h1⟩ := stableResidual_coefficients_bound (w := w) hm
  have hL : 0 < m + 1 := by linarith
  have H := (abs_add_le
    (stableResidual4 m * u ^ 4 + stableResidual3 m * u ^ 3 * w + stableResidual2 m w * u ^ 2 * w ^ 2)
    (stableResidual1 m w * u * w ^ 3)).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  change |stableCorrectedResidual m u w| ≤ _ at H
  simp only [abs_mul, abs_pow] at H
  have H4 := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ |u| ^ 4)
  have H3 := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ |u| ^ 3 * |w|)
  have H2 := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ |u| ^ 2 * |w| ^ 2)
  have H1 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ |u| * |w| ^ 3)
  have hpoly : |u| ^ 4 + |u| ^ 3 * |w| + |u| ^ 2 * |w| ^ 2 + |u| * |w| ^ 3 ≤
      |u| * (|u| + |w|) ^ 3 := by
    nlinarith [show 0 ≤ |u| ^ 3 * |w| by positivity, show 0 ≤ |u| ^ 2 * |w| ^ 2 by positivity]
  have hp := mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 64 / (m + 1))
  nlinarith only [H, H4, H3, H2, H1, hp]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrectedResidual_band_bound {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    |stableCorrectedResidual m u w| ≤ 128 / (c + 1) * |u| * (|u| + |w|) ^ 3 := by
  have hml := (abs_le.mp hm).1
  have hm' : 3 / 2 ≤ m := by linarith
  have hL : 0 < m + 1 := by linarith
  have hK : 0 < c + 1 := by linarith
  have hratio : 64 / (m + 1) ≤ 128 / (c + 1) := by
    apply (div_le_div_iff₀ hL hK).mpr
    linarith
  exact (stableCorrectedResidual_bound hm').trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio (abs_nonneg _)) (by positivity))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_clock_exp_decay_le {z z' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzc : ContinuousOn z' (Icc a b)) :
    (∫ t in a..b, z' t * Real.exp (-c * (z t - z a))) ≤ 1 / c := by
  rw [integral_clock_exp_decay hab hc hz hzc]
  exact (div_le_div_iff_of_pos_right hc).mpr (by linarith [Real.exp_pos (-c * (z b - z a))])

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

theorem solution {m c u w T : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hT : 0 ≤ T) :
    |stableResidualIntegral m u w T| ≤ 1024 * |u| * (|u| + |w|) ^ 3 / (c + 1) ^ 3 := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  let Y := stableBoundaryOrbit m u w
  let a := normalizedProjectiveRate x 0
  let K := c + 1
  let z := normalizedStableClock x 0 0 c
  let C := 128 * |u| * (|u| + |w|) ^ 3 / K ^ 2
  let e := fun t => Real.exp (-K / 8 * z t)
  let B := fun t => C * ((K * a t) * e t)
  have hK : 0 < K := by dsimp [K]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hglobal := stableBoundaryOrbit_global hc hm hu hw
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hdom (t : ℝ) (ht : 0 ≤ t) : t ∈ normalizedMaxDomain x 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hapos (t : ℝ) (ht : 0 ≤ t) : 0 < a t :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) (hglobal t ht).1
  have hY (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_stableBoundaryOrbit hc hm hu hw ht
  have hM (t : ℝ) (ht : 0 ≤ t) : 1 < Y t 0 := by
    have hl := (abs_le.mp (hglobal t ht).2.1.1).1
    linarith
  have hd (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_stableCorrectedPhase_scaled
    (hY t ht) (hM t ht) (hglobal t ht).2.1.2.2.1
  have hz (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt z (K * a t) t :=
    hasDerivAt_normalizedStableClock (hdom 0 le_rfl) (hdom t ht.1)
  have ha : ContinuousOn a (Icc 0 T) := (continuousOn_normalizedProjectiveRate _ _).mono
    (fun t ht => hdom t ht.1)
  have he : ContinuousOn e (Icc 0 T) := Real.continuous_exp.comp_continuousOn
    ((HasDerivAt.continuousOn hz).const_mul (-K / 8))
  have hB : ContinuousOn B (Icc 0 T) := (((ha.const_mul K).mul he).const_mul C)
  have hfast (t : ℝ) (ht : t ∈ Icc 0 T) : |Y t 1| ≤ |u| * e t := by
    have H := (normalized_stable_prefix_estimates hx hc (le_refl 0) hT
      (fun r hr => hapos r hr.1) (fun r hr => (hglobal r hr.1).2.1)).2.1 t ht
    have H' := H.1
    change |Y t 1| ≤ |Y 0 1| * e t at H'
    simpa only [Y, stableBoundaryOrbit_initial, stableBoundaryEntry, Matrix.cons_val_one,
      Matrix.cons_val_zero] using H'
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      |a t * stableCorrectedResidual (Y t 0) (Y t 1) (Y t 3)| ≤ B t := by
    have hsum : |Y t 1| + |Y t 3| ≤ |u| + |w| :=
      add_le_add (hglobal t ht.1).2.2.2.1 (hglobal t ht.1).2.2.2.2
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ |Y t 1| + |Y t 3|) hsum 3
    have hprod := mul_le_mul (hfast t ht) hpow (by positivity : 0 ≤ (|Y t 1| + |Y t 3|) ^ 3)
      (by positivity : 0 ≤ |u| * e t)
    have hR := stableCorrectedResidual_band_bound (u := Y t 1) (w := Y t 3) hc (hglobal t ht.1).2.1.1
    have hR' := hR.trans (by
      convert! mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 128 / K) using 1
      ring)
    rw [abs_mul, abs_of_pos (hapos t ht.1)]
    apply (mul_le_mul_of_nonneg_left hR' (hapos t ht.1).le).trans_eq
    dsimp [B, C]
    field_simp
  have H := abs_sub_le_integral_bound hT (fun t ht => hd t ht.1) hB hbound
  have heq := stableResidualIntegral_eq hc hm hu hw hT
  have hinit : stableCorrectedPhase (Y 0 0) (Y 0 1) (Y 0 3) = stableCorrectedPhase m u w := by
    simp [Y, stableBoundaryOrbit_initial, stableBoundaryEntry]
  change |stableCorrectedApproximation ![m, u, w] T - stableCorrectedPhase (Y 0 0) (Y 0 1) (Y 0 3)| ≤ _ at H
  rw [hinit, ← heq] at H
  have hz0 : z 0 = 0 := by simp [z, normalizedStableClock, integralClock_initial]
  have HI : (∫ t in 0..T, (K * a t) * e t) ≤ 1 / (K / 8) := by
    simpa only [hz0, sub_zero, neg_div, e] using
      integral_clock_exp_decay_le hT (by positivity : 0 < K / 8) hz (ha.const_mul K)
  change |stableResidualIntegral m u w T| ≤ ∫ t in 0..T, C * ((K * a t) * e t) at H
  rw [intervalIntegral.integral_const_mul] at H
  apply H.trans ((mul_le_mul_of_nonneg_left HI hC).trans_eq ?_)
  dsimp [C, K]
  field_simp
  ring
