-- Prove2me | solution 1 for Formalism.ELL.velu_u_series
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:19.913429+00:00
-- url     : https://prove2.me/submissions/47dfad3a-4855-4bb2-b5b6-f912632196cc

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_gx_map
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_gy_map
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_v_map
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_u_map
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_v_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_u_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_c_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_termX
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_termY
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_integral_w
import Theorems.Thm_Formalism_ELL_WeierstrassPointSeriesTail_factor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.G VeluCoordinateMaps
namespace Formalism.ELL
theorem _root_.solution : VeluUSeries.{u} := by
  intro K _ _ W w k S hW hw hS L WL SL x y

  let φ : PowerSeries (unitBall K) →+* PowerSeries K := PowerSeries.map (unitBall K).subtype
  let ι : MvPowerSeries Unit K →+* L := algebraMap (MvPowerSeries Unit K) L
  let ψ : PowerSeries (unitBall K) →+* L := ι.comp φ
  have hφcoeff : ∀ (g : PowerSeries (unitBall K)) (n : ℕ), coeff n (φ g) = ((coeff n g : unitBall K) : K) :=
    fun g n => coeff_map _ n g
  have hψC : ∀ (a : K) (h : a ∈ unitBall K), ψ (C ⟨a, h⟩) = algebraMap K L a := by
    intro a h
    show ι (PowerSeries.map (unitBall K).subtype (C ⟨a, h⟩)) = _
    rw [map_C]
    show algebraMap (MvPowerSeries Unit K) L (C a) = _
    rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  obtain ⟨u, hu⟩ : ∃ u : L, ι (PowerSeries.X : PowerSeries K) = u := ⟨_, rfl⟩
  have hψX : ψ X = u := by
    show ι (PowerSeries.map (unitBall K).subtype X) = u
    rw [map_X, hu]
  have hinj : Function.Injective ι := IsFractionRing.injective _ _
  have hu0 : u ≠ 0 := by
    rw [← hu]; intro h
    exact PowerSeries.X_ne_zero (hinj (by rw [h, map_zero]))

  obtain ⟨e, he⟩ := WeierstrassPointSeriesTail.factor W w hw
  have hwI := FormalGroupPointsParam.integral_w hW hw
  have hUI : ∀ n, ‖coeff n (1 + X * e)‖ ≤ 1 := by
    intro n
    have h := coeff_X_pow_mul (1 + X * e) 3 n
    rw [← he] at h
    rw [← h]; exact hwI _
  obtain ⟨U', hU'⟩ : ∃ U' : PowerSeries (unitBall K), φ U' = 1 + X * e :=
    ⟨PowerSeries.mk fun n => ⟨coeff n (1 + X * e), mem.mpr (hUI n)⟩, by
      ext n; rw [hφcoeff, coeff_mk]⟩
  have hcU : constantCoeff U' = 1 := by
    apply Subtype.ext
    have h := hφcoeff U' 0
    rw [hU'] at h
    rw [← coeff_zero_eq_constantCoeff_apply, ← h]
    simp
  obtain ⟨Ui', hUU'⟩ : ∃ Ui' : PowerSeries (unitBall K), U' * Ui' = 1 :=
    ⟨invOfUnit U' 1, mul_invOfUnit _ _ (by rw [hcU]; rfl)⟩
  have hcUi : constantCoeff Ui' = 1 := by
    have h := congrArg constantCoeff hUU'
    rwa [map_mul, hcU, one_mul, map_one] at h

  let xq : Fin k → unitBall K := fun i => ⟨(S i).1, mem.mpr (hS i).1⟩
  let yq : Fin k → unitBall K := fun i => ⟨(S i).2, mem.mpr (hS i).2⟩
  have hcD : ∀ i, constantCoeff (Ui' - C (xq i) * X ^ 2) = 1 := by
    intro i
    rw [map_sub, map_mul, map_pow, constantCoeff_X, hcUi]
    simp
  have hDex : ∀ i, ∃ D : PowerSeries (unitBall K), (Ui' - C (xq i) * X ^ 2) * D = 1 :=
    fun i => ⟨_, mul_invOfUnit (Ui' - C (xq i) * X ^ 2) 1 (by rw [hcD i]; rfl)⟩
  choose Di hDD using hDex
  let a1' : unitBall K := ⟨W.a₁, mem.mpr hW.1⟩
  let a3' : unitBall K := ⟨W.a₃, mem.mpr hW.2.2.1⟩
  let vq : Fin k → unitBall K := fun i => ⟨veluV W (S i).1 (S i).2, v_mem hW (hS i).1 (hS i).2⟩
  let uq : Fin k → unitBall K := fun i => ⟨veluU W (S i).1 (S i).2, u_mem hW (hS i).1 (hS i).2⟩
  let cq : Fin k → unitBall K := fun i =>
    ⟨W.a₁ * veluU W (S i).1 (S i).2 - veluGx W (S i).1 (S i).2 * veluGy W (S i).1 (S i).2,
      c_mem hW (hS i).1 (hS i).2⟩
  obtain ⟨EX, hEX⟩ : ∃ EX : PowerSeries (unitBall K), EX = Ui' + X ^ 4 *
      ∑ i, (C (vq i) * Di i + C (uq i) * X ^ 2 * Di i ^ 2) := ⟨_, rfl⟩
  obtain ⟨EY, hEY⟩ : ∃ EY : PowerSeries (unitBall K), EY = Ui' + X ^ 4 *
      ∑ i, (C (uq i) * (-2 * Ui' * X ^ 2 + C a1' * Ui' * X ^ 3 + C a3' * X ^ 5) * Di i ^ 3
        + C (vq i) * (C a1' * (Ui' - C (xq i) * X ^ 2) * X - Ui' - C (yq i) * X ^ 3) * Di i ^ 2
        + C (cq i) * X ^ 3 * Di i ^ 2) := ⟨_, rfl⟩
  have hcEX : constantCoeff EX = 1 := by simp [hEX, hcUi]
  have hcEY : constantCoeff EY = 1 := by simp [hEY, hcUi]
  obtain ⟨EYi, hEE⟩ : ∃ EYi : PowerSeries (unitBall K), EY * EYi = 1 :=
    ⟨invOfUnit EY 1, mul_invOfUnit _ _ (by rw [hcEY]; rfl)⟩
  have hcEYi : constantCoeff EYi = 1 := by
    have h := congrArg constantCoeff hEE
    rwa [map_mul, hcEY, one_mul, map_one] at h
  refine ⟨φ (X * EX * EYi), fun n => by rw [hφcoeff]; exact (coeff n (X * EX * EYi)).2, ?_, ?_, ?_⟩
  · rw [hφcoeff, mul_assoc, coeff_zero_X_mul]; rfl
  · rw [hφcoeff, mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, hcEX, hcEYi, one_mul]
    rfl

  have hsub : w.subst (X : PowerSeries K) = w := X_subst w
  have hιw : ι w = u ^ 3 * ψ U' := by
    show ι w = u ^ 3 * ι (φ U')
    rw [hU', ← hu, ← map_pow, ← map_mul, ← he]
  have hUUl : ψ U' * ψ Ui' = 1 := by rw [← map_mul, hUU', map_one]
  have hU0 : ψ U' ≠ 0 := left_ne_zero_of_mul_eq_one hUUl
  have hu30 : u ^ 3 * ψ U' ≠ 0 := mul_ne_zero (pow_ne_zero 3 hu0) hU0
  have hx : x * u ^ 2 = ψ Ui' := by
    show ι (X : PowerSeries K) / ι (w.subst (X : PowerSeries K)) * u ^ 2 = ψ Ui'
    rw [hsub, hιw, hu, div_mul_eq_mul_div, div_eq_iff hu30]
    linear_combination (-u ^ 3) * hUUl
  have hy : y * u ^ 3 = -ψ Ui' := by
    show -1 / ι (w.subst (X : PowerSeries K)) * u ^ 3 = -ψ Ui'
    rw [hsub, hιw, div_mul_eq_mul_div, div_eq_iff hu30]
    linear_combination u ^ 3 * hUUl
  have hxq : ∀ i, ψ (C (xq i)) = (SL i).1 := fun i => hψC _ _
  have hyq : ∀ i, ψ (C (yq i)) = (SL i).2 := fun i => hψC _ _
  have hinv : ∀ i, (x - (SL i).1)⁻¹ = u ^ 2 * ψ (Di i) := by
    intro i
    apply inv_eq_of_mul_eq_one_right
    have h := congrArg ψ (hDD i)
    rw [map_mul, map_sub, map_mul, map_pow, hψX, map_one, hxq] at h
    linear_combination ψ (Di i) * hx + h
  have hv : ∀ i, veluV WL (SL i).1 (SL i).2 = ψ (C (vq i)) := fun i =>
    (v_map (algebraMap K L) W _ _).trans (hψC _ _).symm
  have hU : ∀ i, veluU WL (SL i).1 (SL i).2 = ψ (C (uq i)) := fun i =>
    (u_map (algebraMap K L) W _ _).trans (hψC _ _).symm
  have hc : ∀ i, WL.a₁ * veluU WL (SL i).1 (SL i).2
      - veluGx WL (SL i).1 (SL i).2 * veluGy WL (SL i).1 (SL i).2 = ψ (C (cq i)) := by
    intro i
    rw [hψC, map_sub, map_mul, map_mul, ← u_map, ← gx_map, ← gy_map]
    rfl
  have ha1 : WL.a₁ = ψ (C a1') := (hψC _ _).symm
  have ha3 : WL.a₃ = ψ (C a3') := (hψC _ _).symm
  have hXe : veluX WL SL x * u ^ 2 = ψ EX := by
    have e1 : ψ EX = ψ Ui' + u ^ 4 * ∑ i, (ψ (C (vq i)) * ψ (Di i)
        + ψ (C (uq i)) * u ^ 2 * ψ (Di i) ^ 2) := by
      rw [hEX]; simp only [map_add, map_mul, map_pow, map_sum, hψX]
    rw [e1]
    simp only [veluX]
    rw [add_mul, Finset.sum_mul, hx, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [termX _ _ _ _ _ _ (hinv i), hv i, hU i]
  have hYe : veluY WL SL x y * u ^ 3 = -ψ EY := by
    have e2 : ψ EY = ψ Ui' + u ^ 4 * ∑ i, (ψ (C (uq i)) * (-2 * ψ Ui' * u ^ 2
        + ψ (C a1') * ψ Ui' * u ^ 3 + ψ (C a3') * u ^ 5) * ψ (Di i) ^ 3
        + ψ (C (vq i)) * (ψ (C a1') * (ψ Ui' - ψ (C (xq i)) * u ^ 2) * u - ψ Ui'
          - ψ (C (yq i)) * u ^ 3) * ψ (Di i) ^ 2
        + ψ (C (cq i)) * u ^ 3 * ψ (Di i) ^ 2) := by
      rw [hEY]; simp only [map_add, map_mul, map_pow, map_sum, map_sub, map_neg, map_ofNat, hψX]
    have hs : ∀ i ∈ Finset.univ, (veluU WL (SL i).1 (SL i).2 * (2 * y + WL.a₁ * x + WL.a₃)
          / (x - (SL i).1) ^ 3
        + veluV WL (SL i).1 (SL i).2 * (WL.a₁ * (x - (SL i).1) + y - (SL i).2) / (x - (SL i).1) ^ 2
        + (WL.a₁ * veluU WL (SL i).1 (SL i).2
            - veluGx WL (SL i).1 (SL i).2 * veluGy WL (SL i).1 (SL i).2) / (x - (SL i).1) ^ 2)
          * u ^ 3 =
        u ^ 4 * (ψ (C (uq i)) * (-2 * ψ Ui' * u ^ 2
        + ψ (C a1') * ψ Ui' * u ^ 3 + ψ (C a3') * u ^ 5) * ψ (Di i) ^ 3
        + ψ (C (vq i)) * (ψ (C a1') * (ψ Ui' - ψ (C (xq i)) * u ^ 2) * u - ψ Ui'
          - ψ (C (yq i)) * u ^ 3) * ψ (Di i) ^ 2
        + ψ (C (cq i)) * u ^ 3 * ψ (Di i) ^ 2) := by
      intro i _
      rw [termY _ _ _ _ _ _ _ _ _ _ _ _ (hinv i) hx hy, hc i, hv i, hU i, ha1, ha3, hxq i, hyq i]
    rw [e2]
    simp only [veluY]
    rw [sub_mul, Finset.sum_mul, Finset.sum_congr rfl hs, hy, ← Finset.mul_sum]
    ring
  have hEYl : ψ EY * ψ EYi = 1 := by rw [← map_mul, hEE, map_one]
  have hY0 : veluY WL SL x y ≠ 0 := by
    intro h
    rw [h, zero_mul] at hYe
    have h2 : ψ EY = 0 := by linear_combination hYe
    rw [h2, zero_mul] at hEYl
    exact zero_ne_one hEYl
  show ψ (X * EX * EYi) = _
  rw [map_mul, map_mul, hψX, eq_div_iff hY0]
  apply mul_right_cancel₀ (pow_ne_zero 3 hu0)
  linear_combination (u * ψ EX * ψ EYi) * hYe - (u * ψ EX) * hEYl + u * hXe
end Formalism.ELL
