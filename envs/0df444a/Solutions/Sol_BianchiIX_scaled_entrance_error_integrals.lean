-- Prove2me | solution 1 for BianchiIX.scaled_entrance_error_integrals
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:29:16.542636+00:00
-- url     : https://prove2.me/submissions/646a61dd-25fe-44a1-bb0c-593aed20e285

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


theorem solution {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    (∫ r in s..t, Y r 3 * (a r * entranceClockRate (Y r))) ≤ Y s 3 ∧
      (∫ r in s..t, (Y r 1) ^ 2 * (a r * entranceClockRate (Y r))) ≤ 3 * (Y s 1) ^ 2 / (2 * k) := by
  let z := fun r => Real.log (Y r 2)
  let q := fun r => a r * entranceClockRate (Y r)
  have hk0 : 0 < k := by linarith
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
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
  have hdz (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ z r - z s := sub_nonneg.mpr (hmono hsm hr hr.1)
  have hdec := scaled_entrance_decay hk hY ha hy hv
  have hW (r : ℝ) (hr : r ∈ Icc s t) : Y r 3 ≤ Y s 3 * Real.exp (-1 * (z r - z s)) := by
    have H : Y r 3 ≤ Y s 3 * Real.exp (-(1 + 1 / k) * (z r - z s)) := by
      simpa only [abs_of_nonneg (hy r hr).2.2.2.2.1, abs_of_nonneg (hy s hsm).2.2.2.2.1] using (hdec r hr).2
    apply H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hy s hsm).2.2.2.2.1)
    nlinarith only [mul_nonneg (one_div_pos.mpr hk0).le (hdz r hr)]
  have hU2 (r : ℝ) (hr : r ∈ Icc s t) : (Y r 1) ^ 2 ≤ (Y s 1) ^ 2 * Real.exp (-(2 * k / 3) * (z r - z s)) := by
    have H : Y r 1 ≤ Y s 1 * Real.exp (-(1 + k / 3) * (z r - z s)) := by
      simpa only [abs_of_nonneg (hy r hr).2.2.1.1, abs_of_nonneg (hy s hsm).2.2.1.1] using (hdec r hr).1
    have H' : Y r 1 ≤ Y s 1 * Real.exp (-(k / 3) * (z r - z s)) := H.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hdz r hr])) (hy s hsm).2.2.1.1)
    have hsquare := (sq_le_sq₀ (hy r hr).2.2.1.1 (mul_nonneg (hy s hsm).2.2.1.1 (Real.exp_pos _).le)).mpr H'
    have heq : (Y s 1 * Real.exp (-(k / 3) * (z r - z s))) ^ 2 =
        (Y s 1) ^ 2 * Real.exp (-(2 * k / 3) * (z r - z s)) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    exact hsquare.trans_eq heq
  constructor
  · simpa only [div_one] using integral_clock_le_of_exp_decay hst hz hqc hq
      (by norm_num : (0 : ℝ) < 1) (hy s hsm).2.2.2.2.1 (hcoord 3) hW
  · have H := integral_clock_le_of_exp_decay hst hz hqc hq
      (show 0 < 2 * k / 3 by positivity) (sq_nonneg (Y s 1)) ((hcoord 1).pow 2) hU2
    convert! H using 1
    field_simp
