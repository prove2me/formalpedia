-- Prove2me | solution 1 for BianchiIX.entrance_radius_clock_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:48:49.639247+00:00
-- url     : https://prove2.me/submissions/cce06aaf-c89e-417b-a14e-ca86bb632619

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
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

noncomputable section
open BianchiIX

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

theorem solution {k m u v w : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 < v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    |(-coupling u v w * coreRadius m v + (m - 1) / coreRadius m v * (u - w) ^ 2) /
      connectionSpeed m u v w| ≤ 4 * (u * (v + w) + u ^ 2 + w ^ 2 / k) := by
  let R := coreRadius m v
  let D := connectionSpeed m u v w
  let B := u * (v + w) + u ^ 2
  have hk0 : 0 < k := by linarith
  have hR : 0 < R := coreRadius_pos hv.1
  have hphase := entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2⟩
  have hspeed := entrance_speed_bounds hk hphase hu ⟨hv.1.le, hv.2⟩ hw
  have hD : 0 < D := by dsimp [D]; linarith [hspeed.1]
  have hRD : R / D ≤ 2 := (div_le_iff₀ hD).mpr (by dsimp [R, D]; linarith [(abs_le.mp hr).2, hspeed.1])
  have htR : (m - 1) / R ≤ 1 := by
    apply (div_le_iff₀ hR).mpr
    have he := coreRadius_sq m v
    unfold coreEnergy at he
    dsimp [R]
    nlinarith only [he, hR, hm, sq_nonneg v]
  have htR0 : 0 ≤ (m - 1) / R := div_nonneg (sub_nonneg.mpr hm) hR.le
  have hDi : 1 / D ≤ 2 / k := (div_le_div_iff₀ hD hk0).mpr (by dsimp [D]; linarith [hspeed.1])
  have hC : |coupling u v w| ≤ B := by
    rw [abs_le]
    dsimp [coupling, B]
    constructor <;> nlinarith only [mul_nonneg hu.1 (add_nonneg hv.1.le hw.1), sq_nonneg u]
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hu.1 (add_nonneg hv.1.le hw.1)) (sq_nonneg u)
  have h1 : |-coupling u v w * (R / D)| ≤ 2 * B := by
    rw [abs_mul, abs_neg, abs_of_pos (div_pos hR hD)]
    have H := mul_le_mul hC hRD (div_nonneg hR.le hD.le) hB
    linarith only [H]
  have hnum : (m - 1) / R * (u - w) ^ 2 ≤ u ^ 2 + w ^ 2 := by
    have H := mul_le_mul_of_nonneg_right htR (sq_nonneg (u - w))
    nlinarith only [H, mul_nonneg hu.1 hw.1]
  have h2 : |((m - 1) / R * (u - w) ^ 2) / D| ≤ (u ^ 2 + w ^ 2) * (2 / k) := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg htR0 (sq_nonneg _)) hD.le)]
    calc
      _ ≤ (u ^ 2 + w ^ 2) / D := div_le_div_of_nonneg_right hnum hD.le
      _ = (u ^ 2 + w ^ 2) * (1 / D) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hDi (by positivity)
  have H := (abs_add_le (-coupling u v w * (R / D)) (((m - 1) / R * (u - w) ^ 2) / D)).trans
    (add_le_add h1 h2)
  have heq : (-coupling u v w * R + (m - 1) / R * (u - w) ^ 2) / D =
      -coupling u v w * (R / D) + ((m - 1) / R * (u - w) ^ 2) / D := by ring
  change |(-coupling u v w * R + (m - 1) / R * (u - w) ^ 2) / D| ≤ _
  rw [heq]
  apply H.trans
  have hku : u ^ 2 / k ≤ u ^ 2 := div_le_self (sq_nonneg u) (by linarith)
  have hkw : 0 ≤ w ^ 2 / k := by positivity
  have hBV : 0 ≤ u * (v + w) := mul_nonneg hu.1 (add_nonneg hv.1.le hw.1)
  calc
    2 * B + (u ^ 2 + w ^ 2) * (2 / k) = 2 * B + 2 * (u ^ 2 / k) + 2 * (w ^ 2 / k) := by ring
    _ ≤ 4 * (u * (v + w) + u ^ 2 + w ^ 2 / k) := by dsimp [B]; linarith only [hku, hkw, hBV]
