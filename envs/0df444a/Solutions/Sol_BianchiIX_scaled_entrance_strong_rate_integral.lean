-- Prove2me | solution 1 for BianchiIX.scaled_entrance_strong_rate_integral
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:30:13.560594+00:00
-- url     : https://prove2.me/submissions/40bd3830-5919-4b2a-9c7f-6f8bfb37dffa

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_scaled_entrance_error_integrals
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

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

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

private theorem BianchiIX.entrance_strong_arc_identity {m u v w : ℝ} (hm : m - 1 ≠ 0)
    (hD : connectionSpeed m u v w ≠ 0) :
    connectionStrongRate m u v w / connectionSpeed m u v w =
      -1 - coreRadius m v ^ 2 / (2 * (m - 1)) +
        (2 * v * w - w ^ 2 + u ^ 2 - (2 + coreRadius m v ^ 2 / (m - 1)) * coupling u v w) /
          (2 * connectionSpeed m u v w) := by
  rw [coreRadius_sq]
  dsimp [coreEnergy, connectionStrongRate, connectionSpeed] at *
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_arc_square_coefficient {k m v : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100) (hv : 0 ≤ v ∧ v ≤ 1) :
    coreRadius m v ^ 2 / (m - 1) ≤ 32 / 25 * k := by
  have hp := entrance_phase_bounds hk hm hr hv
  have hk0 : 0 ≤ k := by linarith
  have ht : 0 < m - 1 := by linarith [hp.1]
  have hR0 : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have hRsq := mul_nonneg (show 0 ≤ 101 / 100 * k - coreRadius m v by linarith [(abs_le.mp hr).2])
    (show 0 ≤ 101 / 100 * k + coreRadius m v by positivity)
  have hprod := mul_le_mul_of_nonneg_left hp.1 (show 0 ≤ 32 / 25 * k by positivity)
  apply (div_le_iff₀ ht).mpr
  nlinarith only [hRsq, hprod, sq_nonneg k]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_arc_error_bound {k m u v w : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    (2 * v * w - w ^ 2 + u ^ 2 - (2 + coreRadius m v ^ 2 / (m - 1)) * coupling u v w) /
      (2 * connectionSpeed m u v w) ≤ 2 * w / k + 2 * u ^ 2 := by
  have hk0 : 0 < k := by linarith
  have hp := entrance_phase_bounds hk hm hr hv
  have ht : 0 < m - 1 := by linarith [hp.1]
  have hD := entrance_speed_bounds hk hp hu hv hw
  have hD0 : 0 < connectionSpeed m u v w := by linarith [hD.1]
  have hfrac := entrance_arc_square_coefficient hk hm hr hv
  have hcoef : 3 + coreRadius m v ^ 2 / (m - 1) ≤ 4 * connectionSpeed m u v w := by
    linarith only [hfrac, hD.1, hk]
  have hc0 : 0 ≤ 2 + coreRadius m v ^ 2 / (m - 1) := by positivity
  have hC := (connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩).1
  have hCu := mul_le_mul_of_nonneg_left hC hc0
  have hcoefU := mul_le_mul_of_nonneg_right hcoef (sq_nonneg u)
  have hrem : (2 * v * w - w ^ 2 + u ^ 2 - (2 + coreRadius m v ^ 2 / (m - 1)) * coupling u v w) /
      (2 * connectionSpeed m u v w) ≤ v * w / connectionSpeed m u v w + 2 * u ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * connectionSpeed m u v w)).mpr
    have hid : (v * w / connectionSpeed m u v w + 2 * u ^ 2) * (2 * connectionSpeed m u v w) =
        2 * v * w + 4 * connectionSpeed m u v w * u ^ 2 := by field_simp; ring
    rw [hid]
    nlinarith only [hCu, hcoefU, sq_nonneg w]
  have hvw := mul_le_mul_of_nonneg_right hv.2 hw.1
  have hkw := mul_le_mul_of_nonneg_right (show k ≤ 2 * connectionSpeed m u v w by linarith [hD.1]) hw.1
  have hvwk := mul_le_mul_of_nonneg_right hvw hk0.le
  have hterm : v * w / connectionSpeed m u v w ≤ 2 * w / k :=
    (div_le_div_iff₀ hD0 hk0).mpr (by nlinarith only [hkw, hvwk])
  exact hrem.trans (add_le_add hterm le_rfl)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_arc_damping_lower {k m v : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100) (hv : 0 ≤ v ∧ v ≤ 1) :
    99 * k / 200 ≤ coreRadius m v ^ 2 / (2 * (m - 1)) := by
  have hp := entrance_phase_bounds hk hm hr hv
  have ht : 0 < m - 1 := by linarith [hp.1]
  have hR0 : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  have htR : m - 1 ≤ coreRadius m v := by nlinarith only [he, sq_nonneg v, hR0, hm]
  have hprod := mul_le_mul_of_nonneg_left htR hR0
  have hhalf : coreRadius m v / 2 ≤ coreRadius m v ^ 2 / (2 * (m - 1)) :=
    (le_div_iff₀ (by positivity : 0 < 2 * (m - 1))).mpr (by nlinarith only [hprod])
  exact (show 99 * k / 200 ≤ coreRadius m v / 2 by linarith [(abs_le.mp hr).1]).trans hhalf

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_strong_arc_rate {k m u v w : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    connectionStrongRate m u v w / connectionSpeed m u v w ≤
      -(1 + 99 * k / 200) + 2 * w / k + 2 * u ^ 2 := by
  have hp := entrance_phase_bounds hk hm hr hv
  have hD := entrance_speed_bounds hk hp hu hv hw
  have ht : m - 1 ≠ 0 := by linarith [hp.1]
  have hD0 : connectionSpeed m u v w ≠ 0 := by linarith [hD.1]
  rw [entrance_strong_arc_identity ht hD0]
  have hrem := entrance_arc_error_bound hk hm hr hu hv hw
  have hmain := entrance_arc_damping_lower hk hm hr hv
  linarith only [hrem, hmain]

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
    (∫ r in s..t, a r * connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3)) ≤
      -(1 + 99 * k / 200) * (Real.log (Y t 2) - Real.log (Y s 2)) +
        (2 * Y s 3 + 3 * (Y s 1) ^ 2) / k := by
  let z := fun r => Real.log (Y r 2)
  let q := fun r => a r * entranceClockRate (Y r)
  let c := 1 + 99 * k / 200
  let b := fun r => a r * connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3)
  have hk0 : 0 < k := by linarith
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hbc : ContinuousOn b (Icc s t) := by
    apply hac.mul
    unfold connectionStrongRate
    fun_prop
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hwc : ContinuousOn (fun r => Y r 3 * q r) (Icc s t) := (hcoord 3).mul hqc
  have huc : ContinuousOn (fun r => (Y r 1) ^ 2 * q r) (Icc s t) := ((hcoord 1).pow 2).mul hqc
  have hz (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt z (q r) r :=
    hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hqeq : (∫ r in s..t, q r) = z t - z s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hz r (uIcc_of_le hst ▸ hr)) (hqc.intervalIntegrable_of_Icc hst)
  have hbd (r : ℝ) (hr : r ∈ Icc s t) :
      b r ≤ -c * q r + (2 / k) * (Y r 3 * q r) + 2 * ((Y r 1) ^ 2 * q r) := by
    have hD := entranceRegion_clock_pos hk (hy r hr)
    have H := entrance_strong_arc_rate hk (hy r hr).1 (hy r hr).2.1
      (hy r hr).2.2.1 (hy r hr).2.2.2.1 (hy r hr).2.2.2.2
    have hq : 0 ≤ q r := mul_nonneg (ha r hr) hD.le
    have J := mul_le_mul_of_nonneg_left H hq
    have heq : b r = q r * (connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3) / entranceClockRate (Y r)) := by
      dsimp [b, q]
      field_simp
    rw [heq]
    convert! J using 1
    dsimp [c]
    ring
  have H := intervalIntegral.integral_mono_on (μ := volume) hst (hbc.intervalIntegrable_of_Icc hst)
    (((hqc.const_mul (-c)).add (hwc.const_mul (2 / k)) |>.add (huc.const_mul 2)).intervalIntegrable_of_Icc hst) hbd
  simp only [Pi.add_apply] at H
  have hsum : ContinuousOn (fun r => -c * q r + (2 / k) * (Y r 3 * q r)) (Icc s t) :=
    (hqc.const_mul (-c)).add (hwc.const_mul (2 / k))
  rw [intervalIntegral.integral_add
      (hsum.intervalIntegrable_of_Icc hst)
      ((huc.const_mul 2).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_add ((hqc.const_mul (-c)).intervalIntegrable_of_Icc hst)
      ((hwc.const_mul (2 / k)).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hqeq] at H
  have hi := scaled_entrance_error_integrals hk hst hY hac ha hy hv
  have J := add_le_add
    (add_le_add (le_refl (-c * (z t - z s)))
      (mul_le_mul_of_nonneg_left hi.1 (show 0 ≤ 2 / k by positivity)))
    (mul_le_mul_of_nonneg_left hi.2 (by norm_num : (0 : ℝ) ≤ 2))
  apply H.trans (J.trans_eq ?_)
  dsimp [c, z]
  ring
