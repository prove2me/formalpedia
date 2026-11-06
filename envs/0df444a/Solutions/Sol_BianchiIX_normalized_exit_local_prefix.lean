-- Prove2me | solution 1 for BianchiIX.normalized_exit_local_prefix
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:57:52.692561+00:00
-- url     : https://prove2.me/submissions/bb6ec37a-f33b-494d-872e-cb1597e13b63

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_projectiveDenom_eq
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
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

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_coupling_bound {u v w : ℝ} (hv : 0 ≤ v) :
    |coupling u v w| ≤ |u| * v + (|u| + |w|) ^ 2 := by
  have H : |v + w - u| ≤ v + |w| + |u| := by
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le v w).trans_eq (by rw [abs_of_nonneg hv])) le_rfl)
  rw [coupling, abs_mul]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg u)
  nlinarith only [H', mul_nonneg (abs_nonneg u) (abs_nonneg w), sq_nonneg |w|]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailSpeed_compact {R u v w : ℝ} (hR : 7 / 4 ≤ R)
    (hu : |u| ≤ 1 / 100) (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    1 / 2 ≤ exitTailSpeed R u v w := by
  have ht := (exitTailGap_compact hR hv).1
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have huv : |u| * v ≤ 1 / 100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u), hu]
  have hb : (|u| + |w|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    nlinarith only [hu, hw, abs_nonneg u, abs_nonneg w]
  have H := neg_abs_le (coupling u v w)
  dsimp only [exitTailSpeed]
  linarith only [ht, hc, huv, hb, H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_tail {y : ProjectiveState} (hm : y 0 < 1) :
    exitClockRate y = exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) := by
  dsimp only [exitClockRate, exitTailSpeed]
  rw [exitTailGap_of_coreRadius hm]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_compact {y : ProjectiveState} (hm : y 0 < 1)
    (hR : 7 / 4 ≤ coreRadius (y 0) (y 2))
    (hu : |y 1| ≤ 1 / 100) (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : |y 3| ≤ 1 / 100) :
    1 / 2 ≤ exitClockRate y := by
  rw [exitClockRate_tail hm]
  exact exitTailSpeed_compact hR hu hv hw

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

private theorem BianchiIX.exitPhysicalRegion_phase_bounds {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : -5 ≤ y 0 ∧ y 0 < 0 := by
  have hR0 : 0 ≤ coreRadius (y 0) (y 2) := Real.sqrt_nonneg _
  have he := coreRadius_sq (y 0) (y 2)
  dsimp only [coreEnergy] at he
  have hR2 := (sq_le_sq₀ hR0 (by norm_num : (0 : ℝ) ≤ 17 / 4)).mpr hy.2.1.2
  have hv0 : 0 ≤ y 2 := (hh.trans_le hy.2.2.2.1.1).le
  constructor
  · nlinarith only [he, hR2, sq_nonneg (y 2)]
  · by_contra hn
    have hm0 : y 0 = 0 := le_antisymm hy.1 (le_of_not_gt hn)
    nlinarith only [he, hm0, hv0, hy.2.2.2.1.2, hy.2.1.1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_clock {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 1 / 2 ≤ exitClockRate y :=
  exitClockRate_compact (lt_of_le_of_lt hy.1 (by norm_num)) hy.2.1.1 hy.2.2.1
    ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩ hy.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_denom {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 0 < projectiveStateDenom y ∧ projectiveStateDenom y ≤ 48 := by
  have hm := exitPhysicalRegion_phase_bounds hh hy
  have hm2 : (y 0) ^ 2 ≤ 25 := by nlinarith only [hm.1, hm.2]
  have hu := abs_le.mp hy.2.2.1
  have hw := abs_le.mp hy.2.2.2.2
  have hv : 0 ≤ y 2 ∧ y 2 ≤ 1 := ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩
  have hu2 : (y 1) ^ 2 ≤ 1 := by nlinarith only [hu.1, hu.2]
  have hvw : |y 2 - y 3| ≤ 2 := by
    have H := abs_sub (y 2) (y 3)
    rw [abs_of_nonneg hv.1] at H
    linarith only [H, hv.2, hy.2.2.2.2]
  have hvw2 : (y 2 - y 3) ^ 2 ≤ 4 := by nlinarith only [hvw, abs_nonneg (y 2 - y 3), sq_abs (y 2 - y 3)]
  have hsum : |y 2 + y 3| ≤ 2 := by
    have H := abs_add_le (y 2) (y 3)
    rw [abs_of_nonneg hv.1] at H
    linarith only [H, hv.2, hy.2.2.2.2]
  have hc : |2 * y 1 * (y 2 + y 3)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := mul_le_mul hy.2.2.1 hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    nlinarith only [H]
  change 0 < projectiveDenom (y 0) (y 1) (y 2) (y 3) ∧ projectiveDenom (y 0) (y 1) (y 2) (y 3) ≤ 48
  rw [projectiveDenom_eq]
  constructor
  · nlinarith only [(abs_le.mp hc).2, sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2 - y 3)]
  · nlinarith only [(abs_le.mp hc).1, hm2, hu2, hvw2]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_exit_chart_lower {x : NormalizedState} {h : ℝ} (hh : 0 < h)
    (hA : 1 + x 0 ≠ 0) (hx : stateConstraint x = 1)
    (hy : exitPhysicalRegion h (toProjectiveState x)) : 1 / 8 ≤ 1 + x 0 := by
  have hD := exitPhysicalRegion_denom hh hy
  have H := projective_inverse_scale hA hx
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at H
  rw [← H]
  exact (le_div_iff₀ hD.1).mpr (by linarith only [hD.2])

end
end


theorem solution {x : NormalizedState} {t₀ s h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let y := toProjectiveState (normalizedMaxCurve x t₀ s)
    y 0 < 0 → (7 / 4 < coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) < 17 / 4) →
    |y 1| < 1 / 100 → (h < y 2 ∧ y 2 ≤ 1) → |y 3| < 1 / 100 →
    ∃ r > s, ∀ u ∈ Icc s r, 1 / 16 < 1 + normalizedMaxCurve x t₀ u 0 ∧
      exitPhysicalRegion h (toProjectiveState (normalizedMaxCurve x t₀ u)) := by
  intro y hm hR hu hv hw
  let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
  have hregion : exitPhysicalRegion h y := ⟨hm.le, ⟨hR.1.le, hR.2.le⟩, hu.le, ⟨hv.1.le, hv.2⟩, hw.le⟩
  have hactual := normalizedMaxCurve_forward_of_constraint hc hs
  have hsol : HasDerivAt β ((1 + normalizedMaxCurve x t₀ s 0) • projectiveField (β s)) s :=
    hasDerivAt_toProjectiveState_normalized hactual.1 (ne_of_gt hA) hactual.2.1
  have hcoord (i : Fin 4) := (hasDerivAt_pi.mp hsol i).continuousAt
  have hAc : ContinuousAt (fun u => 1 + normalizedMaxCurve x t₀ u 0) s :=
    continuousAt_const.add (hasDerivAt_pi.mp hactual.1 0).continuousAt
  have hRc : ContinuousAt (fun u => coreRadius (β u 0) (β u 2)) s := by
    unfold coreRadius coreEnergy
    fun_prop
  have hmargin : 1 / 16 < 1 + normalizedMaxCurve x t₀ s 0 :=
    lt_of_lt_of_le (by norm_num) (normalized_exit_chart_lower hh (ne_of_gt hA) hactual.2.1 hregion)
  have hD : 0 < exitClockRate (β s) := by
    have H := exitPhysicalRegion_clock hh hregion
    change 1 / 2 ≤ exitClockRate (β s) at H
    linarith only [H]
  have hVbound : ∀ᶠ u in 𝓝[>] s, β u 2 < 1 := by
    apply eventually_lt_bound_of_deriv_inward (hasDerivAt_pi.mp hsol 2) hv.2
    intro hcap
    change (1 + normalizedMaxCurve x t₀ s 0) * activeVelocity (β s 0) (β s 1) (β s 2) (β s 3) < 0
    have heq : activeVelocity (β s 0) (β s 1) (β s 2) (β s 3) = -exitClockRate (β s) * β s 2 := by
      dsimp only [activeVelocity, exitClockRate]
      ring
    rw [heq, hcap, mul_one]
    exact mul_neg_of_pos_of_neg hA (neg_neg_of_pos hD)
  have H : ∀ᶠ u in 𝓝[>] s, 1 / 16 < 1 + normalizedMaxCurve x t₀ u 0 ∧ exitPhysicalRegion h (β u) := by
    filter_upwards [(hAc.eventually (isOpen_Ioi.mem_nhds hmargin)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 0).eventually (isOpen_Iio.mem_nhds hm)).filter_mono nhdsWithin_le_nhds,
      (hRc.eventually (Ioo_mem_nhds hR.1 hR.2)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 1).abs.eventually (isOpen_Iio.mem_nhds hu)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 2).eventually (isOpen_Ioi.mem_nhds hv.1)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 3).abs.eventually (isOpen_Iio.mem_nhds hw)).filter_mono nhdsWithin_le_nhds, hVbound]
      with u hAu hmu hRu huu hvu hwu hVu
    exact ⟨hAu, hmu.le, ⟨hRu.1.le, hRu.2.le⟩, huu.le, ⟨hvu.le, hVu.le⟩, hwu.le⟩
  obtain ⟨r, hr, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp H
  refine ⟨r, hr, ?_⟩
  intro u hu
  rcases eq_or_lt_of_le hu.1 with heq | hlt
  · subst u
    exact ⟨hmargin, hregion⟩
  · exact hsub ⟨hlt, hu.2⟩
