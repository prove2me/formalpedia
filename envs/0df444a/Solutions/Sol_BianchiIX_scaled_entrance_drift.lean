-- Prove2me | solution 1 for BianchiIX.scaled_entrance_drift
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:56:48.416265+00:00
-- url     : https://prove2.me/submissions/238e3d70-924b-4d19-9d98-45b00b75fb51

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_entrance_radial_envelope
import Theorems.Thm_BianchiIX_entrance_radius_clock_bound
import Theorems.Thm_BianchiIX_integral_clock_exp_decay
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
open Set MeasureTheory

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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_directional {m u v w : ℝ} (hv : 0 < v) :
    ((m - 1) * phaseVelocity m u v w + v * activeVelocity m u v w) / coreRadius m v =
      -coupling u v w * coreRadius m v + (m - 1) / coreRadius m v * (u - w) ^ 2 := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  apply (div_eq_iff hr).mpr
  field_simp
  rw [coreRadius_sq]
  unfold phaseVelocity activeVelocity coupling coreEnergy
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_coreRadius {m v : ℝ → ℝ} {m' v' t : ℝ}
    (hm : HasDerivAt m m' t) (hdv : HasDerivAt v v' t) (hv : 0 < v t) :
    HasDerivAt (fun s => coreRadius (m s) (v s))
      (((m t - 1) * m' + v t * v') / coreRadius (m t) (v t)) t := by
  have he : coreEnergy (m t) (v t) ≠ 0 := by unfold coreEnergy; positivity
  have hd := (((hm.sub_const 1).pow 2).add (hdv.pow 2)).sqrt he
  convert! hd using 1
  dsimp [coreRadius, coreEnergy]
  ring

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

private theorem BianchiIX.hasDerivAt_coreRadius_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hv : 0 < Y t 2) :
    HasDerivAt (fun r => coreRadius (Y r 0) (Y r 2))
      (a * (-coupling (Y t 1) (Y t 2) (Y t 3) * coreRadius (Y t 0) (Y t 2) +
        (Y t 0 - 1) / coreRadius (Y t 0) (Y t 2) * (Y t 1 - Y t 3) ^ 2)) t := by
  convert! hasDerivAt_coreRadius (hasDerivAt_pi.mp hY 0) (hasDerivAt_pi.mp hY 2) hv using 1
  rw [← coreRadius_directional hv]
  change _ = ((Y t 0 - 1) * (a * phaseVelocity _ _ _ _) + Y t 2 * (a * activeVelocity _ _ _ _)) / _
  ring

theorem solution {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    |coreRadius (Y t 0) (Y t 2) - coreRadius (Y s 0) (Y s 2)| ≤
      12 / k * (Y s 1 * (Y s 2 + Y s 3) + (Y s 1) ^ 2 + (Y s 3) ^ 2) := by
  let z := fun r => Real.log (Y r 2)
  let q := fun r => a r * entranceClockRate (Y r)
  let B := Y s 1 * (Y s 2 + Y s 3) + (Y s 1) ^ 2
  let C := (Y s 3) ^ 2 / k
  let e := fun r => Real.exp (-(k / 3) * (z r - z s))
  let f := fun r => Real.exp (-2 * (z r - z s))
  have hk0 : 0 < k := by linarith
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (hy s hsm).2.2.1.1
    (add_nonneg (hv s hsm).le (hy s hsm).2.2.2.2.1)) (sq_nonneg _)
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) hk0.le
  have hz (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt z (q r) r :=
    hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hzmono : MonotoneOn z (Icc s t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t) (HasDerivAt.continuousOn hz)
      (fun r hr => (hz r (interior_subset hr)).hasDerivWithinAt) (fun r hr => hq r (interior_subset hr))
  have hdec := scaled_entrance_decay hk hY ha hy hv
  have henv (r : ℝ) (hr : r ∈ Icc s t) :
      Y r 1 * (Y r 2 + Y r 3) + (Y r 1) ^ 2 + (Y r 3) ^ 2 / k ≤ B * e r + C * f r := by
    have hV : Y r 2 = Y s 2 * Real.exp (z r - z s) := by
      dsimp [z]
      rw [Real.exp_sub, Real.exp_log (hv r hr), Real.exp_log (hv s hsm)]
      field_simp [(hv s hsm).ne']
    apply entrance_radial_envelope hk0 (sub_nonneg.mpr (hzmono hsm hr hr.1))
      (hy s hsm).2.2.1.1 (hv s hsm).le (hy s hsm).2.2.2.2.1
      (hy r hr).2.2.1.1 (hy r hr).2.2.2.2.1 ?_ ?_ hV
    · simpa only [abs_of_nonneg (hy r hr).2.2.1.1, abs_of_nonneg (hy s hsm).2.2.1.1] using (hdec r hr).1
    · simpa only [abs_of_nonneg (hy r hr).2.2.2.2.1, abs_of_nonneg (hy s hsm).2.2.2.2.1] using (hdec r hr).2
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hzc := HasDerivAt.continuousOn hz
  have hec : ContinuousOn e (Icc s t) := Real.continuous_exp.comp_continuousOn
    ((hzc.sub continuousOn_const).const_mul (-(k / 3)))
  have hfc : ContinuousOn f (Icc s t) := Real.continuous_exp.comp_continuousOn
    ((hzc.sub continuousOn_const).const_mul (-2))
  let b := fun r => 4 * B * (q r * e r) + 4 * C * (q r * f r)
  have hbc : ContinuousOn b (Icc s t) := ((hqc.mul hec).const_mul (4 * B)).add
    ((hqc.mul hfc).const_mul (4 * C))
  have hbound (r : ℝ) (hr : r ∈ Icc s t) :
      |a r * (-coupling (Y r 1) (Y r 2) (Y r 3) * coreRadius (Y r 0) (Y r 2) +
        (Y r 0 - 1) / coreRadius (Y r 0) (Y r 2) * (Y r 1 - Y r 3) ^ 2)| ≤ b r := by
    have hD := (entranceRegion_clock_pos hk (hy r hr)).ne'
    have heq : a r * (-coupling (Y r 1) (Y r 2) (Y r 3) * coreRadius (Y r 0) (Y r 2) +
        (Y r 0 - 1) / coreRadius (Y r 0) (Y r 2) * (Y r 1 - Y r 3) ^ 2) =
        q r * ((-coupling (Y r 1) (Y r 2) (Y r 3) * coreRadius (Y r 0) (Y r 2) +
        (Y r 0 - 1) / coreRadius (Y r 0) (Y r 2) * (Y r 1 - Y r 3) ^ 2) / entranceClockRate (Y r)) := by
      dsimp [q]
      field_simp
    rw [heq, abs_mul, abs_of_nonneg (hq r hr)]
    have H := entrance_radius_clock_bound hk (hy r hr).1 (hy r hr).2.1
      (hy r hr).2.2.1 ⟨hv r hr, (hy r hr).2.2.2.1.2⟩ (hy r hr).2.2.2.2
    have J := mul_le_mul_of_nonneg_left (H.trans (mul_le_mul_of_nonneg_left (henv r hr) (by norm_num))) (hq r hr)
    convert! J using 1
    dsimp [b]
    ring
  have H := abs_sub_le_integral_bound hst (fun r hr => hasDerivAt_coreRadius_scaled (hY r hr) (hv r hr)) hbc hbound
  have hqe : ContinuousOn (fun r => q r * e r) (Icc s t) := hqc.mul hec
  have hqf : ContinuousOn (fun r => q r * f r) (Icc s t) := hqc.mul hfc
  rw [show b = (fun r => 4 * B * (q r * e r) + 4 * C * (q r * f r)) from rfl,
    intervalIntegral.integral_add ((hqe.const_mul (4 * B)).intervalIntegrable_of_Icc hst)
      ((hqf.const_mul (4 * C)).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
  have he := integral_clock_exp_decay_le hst (show 0 < k / 3 by positivity) hz hqc
  have hf := integral_clock_exp_decay_le hst (by norm_num : (0 : ℝ) < 2) hz hqc
  have J := add_le_add (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 * B))
    (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 4 * C))
  apply H.trans (J.trans ?_)
  change 4 * B * (1 / (k / 3)) + 4 * C * (1 / 2) ≤ _
  have heq : 4 * B * (1 / (k / 3)) + 4 * C * (1 / 2) =
      (12 * B + 2 * (Y s 3) ^ 2) / k := by dsimp [C]; field_simp; ring
  rw [heq]
  change _ ≤ 12 / k * (B + (Y s 3) ^ 2)
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hk0).mpr (by nlinarith [sq_nonneg (Y s 3)])
