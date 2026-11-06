-- Prove2me | solution 1 for BianchiIX.scaled_entrance_weighted_envelope_integrals
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:26:26.108165+00:00
-- url     : https://prove2.me/submissions/1d5f59f7-0e95-4b12-9332-1c21149b0ac6

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_integral_clock_le_of_exp_decay
import Theorems.Thm_BianchiIX_scaled_entrance_decay
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
import Mathlib.Topology.Instances.Real.Lemmas
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
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open BianchiIX
open Set MeasureTheory

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
open Set

private theorem BianchiIX.continuous_entranceClockRate : Continuous entranceClockRate := by
  unfold entranceClockRate connectionSpeed coupling
  fun_prop

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

private theorem BianchiIX.hasDerivAt_entranceLog_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => Real.log (Y s 2)) (a * entranceClockRate (Y t)) t := by
  convert! (hasDerivAt_pi.mp hY 2).log hv using 1
  change _ = (a * activeVelocity (Y t 0) (Y t 1) (Y t 2) (Y t 3)) / Y t 2
  unfold activeVelocity entranceClockRate connectionSpeed
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.scaled_entrance_wall_budgets {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    (∀ r ∈ Icc s t, Y r 1 ≤ Y s 1 ∧ Y r 3 ≤ Y s 3) ∧
      (∫ r in s..t, Y r 1 * (a r * entranceClockRate (Y r))) ≤ 3 * Y s 1 / k ∧
      (∫ r in s..t, Y r 3 * (a r * entranceClockRate (Y r))) ≤ Y s 3 := by
  let z := fun r => Real.log (Y r 2)
  let q := fun r => a r * entranceClockRate (Y r)
  have hk0 : 0 < k := by linarith
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hz (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt z (q r) r :=
    hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hmono : MonotoneOn z (Icc s t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t) (HasDerivAt.continuousOn hz)
      (fun r hr => (hz r (interior_subset hr)).hasDerivWithinAt) (fun r hr => hq r (interior_subset hr))
  have hdz (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ z r - z s := sub_nonneg.mpr (hmono hs hr hr.1)
  have hdec := scaled_entrance_decay hk hY ha hy hv
  have hU (r : ℝ) (hr : r ∈ Icc s t) : Y r 1 ≤ Y s 1 * Real.exp (-(k / 3) * (z r - z s)) := by
    have H : Y r 1 ≤ Y s 1 * Real.exp (-(1 + k / 3) * (z r - z s)) := by
      simpa only [abs_of_nonneg (hy r hr).2.2.1.1, abs_of_nonneg (hy s hs).2.2.1.1] using (hdec r hr).1
    exact H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hdz r hr])) (hy s hs).2.2.1.1)
  have hW (r : ℝ) (hr : r ∈ Icc s t) : Y r 3 ≤ Y s 3 * Real.exp (-1 * (z r - z s)) := by
    have H : Y r 3 ≤ Y s 3 * Real.exp (-(1 + 1 / k) * (z r - z s)) := by
      simpa only [abs_of_nonneg (hy r hr).2.2.2.2.1, abs_of_nonneg (hy s hs).2.2.2.2.1] using (hdec r hr).2
    apply H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hy s hs).2.2.2.2.1)
    nlinarith only [mul_nonneg (one_div_pos.mpr hk0).le (hdz r hr)]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact ⟨(hU r hr).trans (mul_le_of_le_one_right (hy s hs).2.2.1.1
      (Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hk0.le (hdz r hr)]))),
      (hW r hr).trans (mul_le_of_le_one_right (hy s hs).2.2.2.2.1
      (Real.exp_le_one_iff.mpr (by linarith only [hdz r hr])))⟩
  · convert! integral_clock_le_of_exp_decay hst hz hqc hq
      (show 0 < k / 3 by positivity) (hy s hs).2.2.1.1 (hcoord 1) hU using 1
    ring
  · simpa only [div_one] using integral_clock_le_of_exp_decay hst hz hqc hq
      (by norm_num : (0 : ℝ) < 1) (hy s hs).2.2.2.2.1 (hcoord 3) hW

end
end

/-- Column integrals follow from the two wall budgets without resolving each product separately. -/
theorem solution {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    (∫ r in s..t, (Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3)) *
      (a r * entranceClockRate (Y r))) ≤ 12 * Y s 1 ∧
    (∫ r in s..t, (Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k + Y r 3 * (Y r 1 + Y r 3) / k ^ 3) *
      (a r * entranceClockRate (Y r))) ≤ 6 * Y s 3 / k ^ 2 := by
  let q := fun r => a r * entranceClockRate (Y r)
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hu := (hy s hs).2.2.1.1
  have hw := (hy s hs).2.2.2.2.1
  have hu1 : Y s 1 ≤ 1 := by linarith [(hy s hs).2.2.1.2]
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hUq : IntervalIntegrable (fun r => Y r 1 * q r) volume s t :=
    ((hcoord 1).mul hqc).intervalIntegrable_of_Icc hst
  have hWq : IntervalIntegrable (fun r => Y r 3 * q r) volume s t :=
    ((hcoord 3).mul hqc).intervalIntegrable_of_Icc hst
  obtain ⟨hwall, hIU, hIW⟩ := scaled_entrance_wall_budgets hk hst hY hac ha hy hv
  change (∫ r in s..t, Y r 1 * q r) ≤ _ at hIU
  change (∫ r in s..t, Y r 3 * q r) ≤ _ at hIW
  constructor
  · have hc : ContinuousOn (fun r => (Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3)) * q r) (Icc s t) :=
      ((hcoord 1).add (((hcoord 1).const_mul k).mul (((hcoord 2).add (hcoord 1)).add (hcoord 3)))).mul hqc
    have HB := intervalIntegral.integral_mono_on hst (hc.intervalIntegrable_of_Icc hst)
      (hUq.const_mul (1 + 3 * k)) (fun r hr => show
        (Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3)) * q r ≤ (1 + 3 * k) * (Y r 1 * q r) from by
          have hsum : Y r 2 + Y r 1 + Y r 3 ≤ 3 := by
            linarith [(hy r hr).2.2.2.1.2, (hy r hr).2.2.1.2, (hy r hr).2.2.2.2.2]
          have hb : Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3) ≤ (1 + 3 * k) * Y r 1 := by
            nlinarith only [mul_le_mul_of_nonneg_left hsum (mul_nonneg hk0.le (hy r hr).2.2.1.1)]
          convert! mul_le_mul_of_nonneg_right hb (hq r hr) using 1
          ring)
    rw [intervalIntegral.integral_const_mul] at HB
    apply HB.trans ((mul_le_mul_of_nonneg_left hIU (by positivity)).trans ?_)
    calc
      (1 + 3 * k) * (3 * Y s 1 / k) = 3 * Y s 1 / k + 9 * Y s 1 := by field_simp; ring
      _ ≤ 12 * Y s 1 := by linarith only [div_le_self (by positivity : 0 ≤ 3 * Y s 1) hk1]
  · have hc : ContinuousOn (fun r => (Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k +
        Y r 3 * (Y r 1 + Y r 3) / k ^ 3) * q r) (Icc s t) :=
      ((((hcoord 3).div_const (k ^ 2)).add (((hcoord 1).mul (hcoord 3)).div_const k)).add
        (((hcoord 3).mul ((hcoord 1).add (hcoord 3))).div_const (k ^ 3))).mul hqc
    have HB := intervalIntegral.integral_mono_on hst (hc.intervalIntegrable_of_Icc hst)
      ((hUq.const_mul (Y s 3 / k)).add (hWq.const_mul (1 / k ^ 2 + 2 / k ^ 3)))
      (fun r hr => show (Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k + Y r 3 * (Y r 1 + Y r 3) / k ^ 3) * q r ≤
        (Y s 3 / k) * (Y r 1 * q r) + (1 / k ^ 2 + 2 / k ^ 3) * (Y r 3 * q r) from by
          have hUW := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hwall r hr).2 (hy r hr).2.2.1.1) hk0.le
          have hsum : Y r 1 + Y r 3 ≤ 2 := by linarith [(hy r hr).2.2.1.2, (hy r hr).2.2.2.2.2]
          have hWW := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum (hy r hr).2.2.2.2.1) (pow_nonneg hk0.le 3)
          have hb' : Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k + Y r 3 * (Y r 1 + Y r 3) / k ^ 3 ≤
              Y r 3 / k ^ 2 + Y r 1 * Y s 3 / k + Y r 3 * 2 / k ^ 3 :=
            add_le_add (add_le_add le_rfl hUW) hWW
          convert! mul_le_mul_of_nonneg_right hb' (hq r hr) using 1
          ring)
    rw [intervalIntegral.integral_add (hUq.const_mul (Y s 3 / k))
      (hWq.const_mul (1 / k ^ 2 + 2 / k ^ 3)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at HB
    apply HB.trans ((add_le_add (mul_le_mul_of_nonneg_left hIU (by positivity))
      (mul_le_mul_of_nonneg_left hIW (by positivity))).trans ?_)
    calc
      (Y s 3 / k) * (3 * Y s 1 / k) + (1 / k ^ 2 + 2 / k ^ 3) * Y s 3 =
          (Y s 3 / k ^ 2) * (3 * Y s 1 + 1 + 2 / k) := by field_simp; ring
      _ ≤ (Y s 3 / k ^ 2) * 6 := mul_le_mul_of_nonneg_left
        (by linarith only [hu1, div_le_self (by norm_num : (0 : ℝ) ≤ 2) hk1]) (by positivity)
      _ = _ := by ring
