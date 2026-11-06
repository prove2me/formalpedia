-- Prove2me | solution 1 for BianchiIX.normalized_entrance_local_prefix
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:57:52.064769+00:00
-- url     : https://prove2.me/submissions/3b7fa2bf-515f-4f3e-b860-6d3cdb311f87

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_entrance_strong_clock_rate
import Theorems.Thm_BianchiIX_entrance_weak_clock_rate
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_projective_inverse_scale
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_gt_right_of_deriv_pos {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hd : 0 < d) : ∀ᶠ t in 𝓝[>] a, f a < f t := by
  have H := (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)).eventually
    (isOpen_Ioi.mem_nhds hd)
  filter_upwards [H, self_mem_nhdsWithin] with t ht hat
  rw [slope_def_field] at ht
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hat)).mp ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_lt_right_of_deriv_neg {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hd : d < 0) : ∀ᶠ t in 𝓝[>] a, f t < f a := by
  have H := eventually_gt_right_of_deriv_pos hf.neg (neg_pos.mpr hd)
  exact H.mono fun _ h => neg_lt_neg_iff.mp h

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_speed_bounds {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    3 / 4 * k ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ 21 / 20 * k := by
  have hC := connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hm.1, hm.2, hC.1, hC.2, hu.2, hu2, hk]

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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_lt_bound_of_deriv_inward {f : ℝ → ℝ} {s d B : ℝ}
    (hf : HasDerivAt f d s) (hle : f s ≤ B) (hinward : f s = B → d < 0) :
    ∀ᶠ t in 𝓝[>] s, f t < B := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (hf.continuousAt.eventually (isOpen_Iio.mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
  · simpa only [heq] using eventually_lt_right_of_deriv_neg hf (hinward heq)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_phase {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    4 / 5 * k ≤ y 0 - 1 ∧ y 0 - 1 ≤ 101 / 100 * k :=
  entrance_phase_bounds hk hy.1 hy.2.1 hy.2.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_speed {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    3 / 4 * k ≤ entranceClockRate y ∧ entranceClockRate y ≤ 21 / 20 * k :=
  entrance_speed_bounds hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_clock_pos {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    0 < entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_wall_rates {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    connectionStrongRate (y 0) (y 1) (y 2) (y 3) / entranceClockRate y ≤ -(1 + k / 3) ∧
      (-y 0 - 1 - coupling (y 1) (y 2) (y 3)) / entranceClockRate y ≤ -(1 + 1 / k) :=
  ⟨entrance_strong_clock_rate hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2,
    entrance_weak_clock_rate hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_entrance_chart_lower {x : NormalizedState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1)
    (hy : entranceRegion k (toProjectiveState x)) : 1 / (k + 1) ^ 2 ≤ 1 + x 0 := by
  have hD := entrance_denom_bounds hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2
  have hscale := projective_inverse_scale hA hc
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at hscale
  rw [← hscale]
  change 1 / (k + 1) ^ 2 ≤ 6 / projectiveDenom _ _ _ _
  calc
    _ = 6 / (6 * (k + 1) ^ 2) := by
      have hK : k + 1 ≠ 0 := by linarith
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hD.1 hD.2

end
end

theorem solution {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    1 ≤ Y s 0 → |coreRadius (Y s 0) (Y s 2) - k| < k / 100 →
    (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
    (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
    ∃ r > s, ∀ b ∈ Icc s r,
      1 / (2 * (k + 1) ^ 2) < normalizedProjectiveRate x t₀ b ∧ entranceRegion k (Y b) := by
  intro Y hm hR hu hv hw
  have hk0 : 0 < k := by linarith
  have hK : 0 < k + 1 := by linarith
  have hregion : entranceRegion k (Y s) := ⟨hm, hR.le, hu, ⟨hv.1.le, hv.2.le⟩, hw⟩
  have hactual := normalizedMaxCurve_forward_of_constraint hc hs
  have hsol : HasDerivAt Y (normalizedProjectiveRate x t₀ s • projectiveField (Y s)) s :=
    hasDerivAt_toProjectiveState_normalized hactual.1 hA.ne' hactual.2.1
  have hcoord (i : Fin 4) : ContinuousAt (fun b => Y b i) s := (hasDerivAt_pi.mp hsol i).continuousAt
  have hAc : ContinuousAt (normalizedProjectiveRate x t₀) s :=
    continuousAt_const.add (hasDerivAt_pi.mp hactual.1 0).continuousAt
  have hRc : ContinuousAt (fun b => |coreRadius (Y b 0) (Y b 2) - k|) s := by
    unfold coreRadius coreEnergy
    fun_prop
  have hms : 1 < Y s 0 := by linarith [(entranceRegion_phase hk hregion).1]
  have hscale := normalized_entrance_chart_lower hk hA.ne' hactual.2.1 hregion
  have hmargin : 1 / (2 * (k + 1) ^ 2) < normalizedProjectiveRate x t₀ s := by
    apply lt_of_lt_of_le _ hscale
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [sq_pos_of_pos hK]
  have hD := entranceRegion_clock_pos hk hregion
  have hrates := entranceRegion_wall_rates hk hregion
  have hUbound : ∀ᶠ b in 𝓝[>] s, Y b 1 < 1 / 10000 := by
    apply eventually_lt_bound_of_deriv_inward (hasDerivAt_pi.mp hsol 1) hu.2
    intro hcap
    have hrate : connectionStrongRate (Y s 0) (Y s 1) (Y s 2) (Y s 3) < 0 :=
      ((div_le_iff₀ hD).mp hrates.1).trans_lt (mul_neg_of_neg_of_pos (by linarith) hD)
    have hwall : 0 < Y s 1 := by rw [hcap]; norm_num
    have hvel : strongVelocity (Y s 0) (Y s 1) (Y s 2) (Y s 3) < 0 := by
      convert! mul_neg_of_neg_of_pos hrate hwall using 1
      unfold strongVelocity connectionStrongRate
      ring
    exact mul_neg_of_pos_of_neg hA hvel
  have hWbound : ∀ᶠ b in 𝓝[>] s, Y b 3 < 1 / 10000 := by
    apply eventually_lt_bound_of_deriv_inward (hasDerivAt_pi.mp hsol 3) hw.2
    intro hcap
    have hrate : -Y s 0 - 1 - coupling (Y s 1) (Y s 2) (Y s 3) < 0 :=
      ((div_le_iff₀ hD).mp hrates.2).trans_lt (mul_neg_of_neg_of_pos (by have := one_div_pos.mpr hk0; linarith) hD)
    have hwall : 0 < Y s 3 := by rw [hcap]; norm_num
    exact mul_neg_of_pos_of_neg hA (mul_neg_of_neg_of_pos hrate hwall)
  have H : ∀ᶠ b in 𝓝[>] s,
      1 / (2 * (k + 1) ^ 2) < normalizedProjectiveRate x t₀ b ∧ 1 < Y b 0 ∧
      |coreRadius (Y b 0) (Y b 2) - k| < k / 100 ∧ Y b 1 < 1 / 10000 ∧ Y b 2 < 1 ∧ Y b 3 < 1 / 10000 := by
    filter_upwards [(hAc.eventually (isOpen_Ioi.mem_nhds hmargin)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 0).eventually (isOpen_Ioi.mem_nhds hms)).filter_mono nhdsWithin_le_nhds,
      (hRc.eventually (isOpen_Iio.mem_nhds hR)).filter_mono nhdsWithin_le_nhds, hUbound,
      ((hcoord 2).eventually (isOpen_Iio.mem_nhds hv.2)).filter_mono nhdsWithin_le_nhds, hWbound]
      with b hAb hmb hRb hub hvb hwb
    exact ⟨hAb, hmb, hRb, hub, hvb, hwb⟩
  obtain ⟨r, hsr, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp H
  refine ⟨r, hsr, ?_⟩
  intro b hb
  rcases eq_or_lt_of_le hb.1 with heq | hlt
  · subst b
    exact ⟨hmargin, hregion⟩
  have Hb := hsub ⟨hlt, hb.2⟩
  have hAb : 0 < normalizedProjectiveRate x t₀ b :=
    lt_trans (by positivity : 0 < 1 / (2 * (k + 1) ^ 2)) Hb.1
  have hdom (c : ℝ) (hh : s ≤ c) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh)
  have hwall (i : Fin 3) := (normalized_projective_wall_sign (hdom s le_rfl) (hdom b hlt.le) hA hAb i).2
  exact ⟨Hb.1, Hb.2.1.le, Hb.2.2.1.le, ⟨(hwall 0).mpr hu.1, Hb.2.2.2.1.le⟩,
    ⟨(hwall 1).mpr hv.1.le, Hb.2.2.2.2.1.le⟩, (hwall 2).mpr hw.1, Hb.2.2.2.2.2.le⟩
