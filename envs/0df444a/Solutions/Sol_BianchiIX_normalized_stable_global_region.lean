-- Prove2me | solution 1 for BianchiIX.normalized_stable_global_region
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:13:01.945293+00:00
-- url     : https://prove2.me/submissions/6b6b8fa7-8651-4683-9332-5218e002a26c

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Theorems.Thm_BianchiIX_scaled_stable_boundary_drift
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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

noncomputable section
open BianchiIX
open Set Filter
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

private theorem BianchiIX.isClosed_stableBoundaryRegion (c : ℝ) :
    IsClosed {y : ProjectiveState | stableBoundaryRegion c y} := by
  have hm : Continuous (fun y : ProjectiveState => |y 0 - c|) := by fun_prop
  exact (isClosed_le hm continuous_const).inter
    ((isClosed_le (continuous_apply 1).abs continuous_const).inter
      ((isClosed_eq (continuous_apply 2) continuous_const).inter
        (isClosed_le (continuous_apply 3).abs continuous_const)))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.normalized_stable_chart_lower {x : NormalizedState} {c : ℝ}
    (hc : 2 ≤ c) (hA : 1 + x 0 ≠ 0) (hx : stateConstraint x = 1)
    (hy : stableBoundaryRegion c (toProjectiveState x)) :
    3 / (c + 1) ^ 2 ≤ 1 + x 0 := by
  have hD := stable_boundary_denom hc hy.1 hy.2.1 hy.2.2.2
  have hscale := projective_inverse_scale hA hx
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at hscale
  rw [← hscale]
  have heq : projectiveStateDenom (toProjectiveState x) =
      projectiveDenom (toProjectiveState x 0) (toProjectiveState x 1) 0 (toProjectiveState x 3) := by
    unfold projectiveStateDenom
    rw [hy.2.2.1]
  rw [heq]
  have hK : 0 < c + 1 := by linarith
  calc
    _ = 6 / (2 * (c + 1) ^ 2) := by field_simp; norm_num
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hD.1 hD.2

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
open Set Filter
open scoped Topology

private theorem BianchiIX.toProjectiveState_wall_sign {x : NormalizedState} (hA : 0 < 1 + x 0) (i : Fin 3) :
    (toProjectiveState x i.succ = 0 ↔ wallValue i x = 0) ∧
      (0 ≤ toProjectiveState x i.succ ↔ 0 ≤ wallValue i x) := by
  have heq : toProjectiveState x i.succ = Real.sqrt 3 * wallValue i x / (1 + x 0) := by
    fin_cases i <;> rfl
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq]
  constructor
  · simp only [div_eq_zero_iff, mul_eq_zero, ne_of_gt hsqrt, ne_of_gt hA, false_or, or_false]
  · rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.mpr hA), mul_nonneg_iff_of_pos_left hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_projective_wall_sign {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (β t i.succ = 0 ↔ β s i.succ = 0) ∧ (0 ≤ β t i.succ ↔ 0 ≤ β s i.succ) := by
  have H := normalized_wall_sign (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
    (fun _ hh => hasDerivAt_normalizedMaxCurve hh) hs ht i
  exact ⟨(toProjectiveState_wall_sign hAt i).1.trans (H.1.trans (toProjectiveState_wall_sign hAs i).1.symm),
    (toProjectiveState_wall_sign hAt i).2.trans (H.2.trans (toProjectiveState_wall_sign hAs i).2.symm)⟩

end
end

private theorem BianchiIX.isClosed_normalized_stable_times {x : NormalizedState} {t₀ s T c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) :
    IsClosed ({r | 3 / (2 * (c + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧
      stableBoundaryRegion c (toProjectiveState (normalizedMaxCurve x t₀ r))} ∩ Icc s T) := by
  let A := normalizedProjectiveRate x t₀
  let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
  let d := 3 / (2 * (c + 1) ^ 2)
  have hd : 0 < d := by
    dsimp [d]
    have : 0 < c + 1 := by linarith
    positivity
  have hα (r : ℝ) (hr : r ∈ Icc s T) :=
    (normalizedMaxCurve_forward_of_constraint hx (hs.trans hr.1)).1.continuousAt
  have hAc : ContinuousOn A (Icc s T) := fun r hr =>
    (continuousAt_const.add ((continuous_apply 0).continuousAt.comp (hα r hr))).continuousWithinAt
  have hD : IsClosed (Icc s T ∩ {r | d ≤ A r}) :=
    hAc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hY : ContinuousOn Y (Icc s T ∩ {r | d ≤ A r}) := by
    intro r hr
    exact ((contDiffAt_toProjectiveState 1 (ne_of_gt (hd.trans_le hr.2))).continuousAt.comp
      (hα r hr.1)).continuousWithinAt
  have H := hY.preimage_isClosed_of_isClosed hD (isClosed_stableBoundaryRegion c)
  convert! H using 1
  ext r
  change (d ≤ A r ∧ stableBoundaryRegion c (Y r)) ∧ r ∈ Icc s T ↔
    (r ∈ Icc s T ∧ d ≤ A r) ∧ stableBoundaryRegion c (Y r)
  tauto

private theorem BianchiIX.normalized_stable_local_prefix {x : NormalizedState} {t₀ s c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y s 0 - c| < 1 / 10 → |Y s 1| < 1 / 100 → Y s 2 = 0 → |Y s 3| < 1 / 100 →
    ∃ T > s, ∀ r ∈ Icc s T,
      3 / (2 * (c + 1) ^ 2) < normalizedProjectiveRate x t₀ r ∧ stableBoundaryRegion c (Y r) := by
  intro Y hm hu hv hw
  have hactual := normalizedMaxCurve_forward_of_constraint hx hs
  have hsol : HasDerivAt Y (normalizedProjectiveRate x t₀ s • projectiveField (Y s)) s :=
    hasDerivAt_toProjectiveState_normalized hactual.1 (ne_of_gt hA) hactual.2.1
  have hcoord (i : Fin 4) := (hasDerivAt_pi.mp hsol i).continuousAt
  have hAc : ContinuousAt (normalizedProjectiveRate x t₀) s :=
    continuousAt_const.add (hasDerivAt_pi.mp hactual.1 0).continuousAt
  have hK : 0 < c + 1 := by linarith
  have hmargin : 3 / (2 * (c + 1) ^ 2) < normalizedProjectiveRate x t₀ s := by
    apply lt_of_lt_of_le _ (normalized_stable_chart_lower hc (ne_of_gt hA) hactual.2.1
      ⟨hm.le, hu.le, hv, hw.le⟩)
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [sq_pos_of_pos hK]
  have H : ∀ᶠ r in 𝓝[>] s,
      3 / (2 * (c + 1) ^ 2) < normalizedProjectiveRate x t₀ r ∧
      |Y r 0 - c| < 1 / 10 ∧ |Y r 1| < 1 / 100 ∧ |Y r 3| < 1 / 100 := by
    filter_upwards [(hAc.eventually (isOpen_Ioi.mem_nhds hmargin)).filter_mono nhdsWithin_le_nhds,
      (((hcoord 0).sub continuousAt_const).abs.eventually (isOpen_Iio.mem_nhds hm)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 1).abs.eventually (isOpen_Iio.mem_nhds hu)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 3).abs.eventually (isOpen_Iio.mem_nhds hw)).filter_mono nhdsWithin_le_nhds]
      with r hr hm hu hw
    exact ⟨hr, hm, hu, hw⟩
  obtain ⟨T, hT, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp H
  refine ⟨T, hT, ?_⟩
  intro r hr
  rcases eq_or_lt_of_le hr.1 with heq | hlt
  · subst r
    exact ⟨hmargin, hm.le, hu.le, hv, hw.le⟩
  have H := hsub ⟨hlt, hr.2⟩
  have hAr : 0 < normalizedProjectiveRate x t₀ r :=
    lt_trans (by positivity : 0 < 3 / (2 * (c + 1) ^ 2)) H.1
  have hVr := (normalized_projective_wall_sign
    (normalizedMaxDomain_contains_Ici_of_constraint hx t₀ hs)
    (normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hlt.le)) hA hAr 1).1.mpr hv
  exact ⟨H.1, H.2.1.le, H.2.2.1.le, hVr, H.2.2.2.le⟩

/-- The actual signed boundary flow stays in one fixed chart for all future time. -/
theorem solution {x : NormalizedState} {t₀ s c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y s 0 - c| ≤ 1 / 40 → |Y s 1| ≤ 1 / 200 → Y s 2 = 0 → |Y s 3| ≤ 1 / 200 →
    ∀ r ≥ s, 3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate x t₀ r ∧
      stableBoundaryRegion c (Y r) ∧
      |Y r 0 - Y s 0| ≤ 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) ∧
      |Y r 1| ≤ |Y s 1| ∧ |Y r 3| ≤ |Y s 3| := by
  intro Y hm hu hv hw T hT
  let d := 3 / (2 * (c + 1) ^ 2)
  have hK : 0 < c + 1 := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  let S := {r | d ≤ normalizedProjectiveRate x t₀ r ∧ stableBoundaryRegion c (Y r)}
  obtain ⟨r₀, hr₀, hprefix⟩ := normalized_stable_local_prefix hx hc hs hA
    (by linarith : |Y s 0 - c| < 1 / 10) (by linarith : |Y s 1| < 1 / 100)
    hv (by linarith : |Y s 3| < 1 / 100)
  have hsS : s ∈ S := ⟨(hprefix s ⟨le_rfl, hr₀.le⟩).1.le, (hprefix s ⟨le_rfl, hr₀.le⟩).2⟩
  have hbudget : 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) < 1 / 40 := by
    apply (div_lt_iff₀ hK).mpr
    have hb0 : 0 ≤ |Y s 1| + |Y s 3| := by positivity
    have hb : |Y s 1| + |Y s 3| ≤ 1 / 100 := by linarith
    have hb2 := (sq_le_sq₀ hb0 (by norm_num : (0 : ℝ) ≤ 1 / 100)).mpr hb
    nlinarith
  have hwhole : Icc s T ⊆ S := by
    apply (isClosed_normalized_stable_times hx hc hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
    intro t ht hbefore
    have htS := hbefore ⟨ht.1, le_rfl⟩
    have hAt : 0 < normalizedProjectiveRate x t₀ t := hd.trans_le htS.1
    have H := normalized_stable_prefix_estimates hx hc hs ht.1
      (fun r hr => hd.trans_le (hbefore hr).1) (fun r hr => (hbefore hr).2)
    have hMt : |Y t 0 - c| < 1 / 10 := by
      have htri : |Y t 0 - c| ≤ |Y t 0 - Y s 0| + |Y s 0 - c| := by
        exact abs_sub_le (Y t 0) (Y s 0) c
      have hsmall := H.1.trans_lt hbudget
      linarith
    have hU := (H.2.2 t ⟨ht.1, le_rfl⟩).1.trans hu
    have hW := (H.2.2 t ⟨ht.1, le_rfl⟩).2.trans hw
    obtain ⟨r, htr, hafter⟩ := normalized_stable_local_prefix hx hc (hs.trans ht.1) hAt hMt
      (by linarith : |Y t 1| < 1 / 100) htS.2.2.2.1 (by linarith : |Y t 3| < 1 / 100)
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    exact ⟨r, htr, fun q hq => ⟨(hafter q ⟨hq.1.le, hq.2⟩).1.le, (hafter q ⟨hq.1.le, hq.2⟩).2⟩⟩
  have htS := hwhole ⟨hT, le_rfl⟩
  have H := normalized_stable_prefix_estimates hx hc hs hT
    (fun r hr => hd.trans_le (hwhole hr).1) (fun r hr => (hwhole hr).2)
  exact ⟨normalized_stable_chart_lower hc (ne_of_gt (hd.trans_le htS.1))
      (normalizedMaxCurve_forward_of_constraint hx (hs.trans hT)).2.1 htS.2,
    htS.2, H.1, H.2.2 T ⟨hT, le_rfl⟩⟩
