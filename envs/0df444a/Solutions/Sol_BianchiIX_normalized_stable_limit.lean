-- Prove2me | solution 1 for BianchiIX.normalized_stable_limit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:16:43.774106+00:00
-- url     : https://prove2.me/submissions/ca55e7a9-4632-47a5-b24f-b134e38d5449

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_stable_global_region
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
import Mathlib.Topology.MetricSpace.Cauchy

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

theorem solution {x : NormalizedState} {t₀ s c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y s 0 - c| ≤ 1 / 40 → |Y s 1| ≤ 1 / 200 → Y s 2 = 0 → |Y s 3| ≤ 1 / 200 →
    ∃ P : ℝ, Tendsto (fun r => Y r 0) atTop (𝓝 P) ∧
      Tendsto (fun r => Y r 1) atTop (𝓝 0) ∧ Tendsto (fun r => Y r 3) atTop (𝓝 0) ∧
      ∀ r ≥ s, |P - Y r 0| ≤ 8 * (|Y r 1| + |Y r 3|) ^ 2 / (c + 1) := by
  intro Y hm hu hv hw
  have hglobal := normalized_stable_global_region hx hc hs hA hm hu hv hw
  have hK : 0 < c + 1 := by linarith
  have hpos : 0 < 3 / (c + 1) ^ 2 := by positivity
  have hclock : Tendsto (normalizedStableClock x t₀ s c) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (Tendsto.const_mul_atTop (by positivity : 0 < 3 / (c + 1))
        (tendsto_atTop_add_const_right atTop (-s) tendsto_id))
    filter_upwards [eventually_ge_atTop s] with t ht
    simpa only [sub_eq_add_neg, id_eq] using normalizedStableClock_lower hx hc hs ht
      (fun r hr => (hglobal r hr.1).1)
  have hdec (t : ℝ) (ht : s ≤ t) :=
    (normalized_stable_prefix_estimates hx hc hs ht
      (fun r hr => hpos.trans_le (hglobal r hr.1).1)
      (fun r hr => (hglobal r hr.1).2.1)).2.1 t ⟨ht, le_rfl⟩
  have hexp (q : ℝ) (hq : 0 < q) :
      Tendsto (fun t => Real.exp (-q * normalizedStableClock x t₀ s c t)) atTop (𝓝 0) := by
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hq hclock) using 1
    ext t
    congr 1
    ring
  have hUabs : Tendsto (fun t => |Y t 1|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa only [mul_zero] using (hexp ((c + 1) / 8) (by positivity)).const_mul |Y s 1|)
    filter_upwards [eventually_ge_atTop s] with t ht
    simpa only [neg_div] using (hdec t ht).1
  have hWabs : Tendsto (fun t => |Y t 3|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa only [mul_zero] using (hexp (1 / 4) (by norm_num)).const_mul |Y s 3|)
    filter_upwards [eventually_ge_atTop s] with t ht
    exact (hdec t ht).2
  let B := fun r => 8 * (|Y r 1| + |Y r 3|) ^ 2 / (c + 1)
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [B, zero_add, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_div] using
      (((hUabs.add hWabs).pow 2).const_mul 8).div_const (c + 1)
  have hpair (r : ℝ) (hr : s ≤ r) (t : ℝ) (ht : r ≤ t) : |Y t 0 - Y r 0| ≤ B r :=
    (normalized_stable_prefix_estimates hx hc (hs.trans hr) ht
      (fun q hq => hpos.trans_le (hglobal q (hr.trans hq.1)).1)
      (fun q hq => (hglobal q (hr.trans hq.1)).2.1)).1
  have hC : CauchySeq (fun r : ℝ => Y r 0) := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.mp (hB.eventually (gt_mem_nhds hε))
    refine ⟨max R s, fun t ht => ?_⟩
    rw [Real.dist_eq]
    exact (hpair (max R s) (le_max_right _ _) t ht).trans_lt (hR _ (le_max_left _ _))
  obtain ⟨P, hP⟩ := cauchy_map_iff_exists_tendsto.mp hC
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hUabs
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hWabs
  · intro r hr
    apply le_of_tendsto ((hP.sub_const (Y r 0)).abs)
    filter_upwards [eventually_ge_atTop r] with t ht
    exact hpair r hr t ht
