-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_or_exists_isTranslateOdd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bf674d08-3507-5245-bd90-473da979f3f5

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_of_det_eq_algebraMap
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateOdd_of_det_mul_eq_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_or_exists_isTranslateOdd

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace E33TE

theorem exists_eq_unit_mul_zpow {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (x : Kˣ) :
    ∃ (n : ℤ) (u : 𝒪ˣ), (x : K) = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ n := by
  have hπK : algebraMap 𝒪 K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr hπ.ne_zero
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := 𝒪) (x : K)
  have ha : a ≠ 0 := by
    rintro rfl; rw [map_zero, zero_div] at hx; exact x.ne_zero hx.symm
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨i, ua, hua⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hπ
  obtain ⟨j, ub, hub⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ
  refine ⟨(i : ℤ) - (j : ℤ), ua⁻¹ * ub, ?_⟩
  have hbK : algebraMap 𝒪 K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr hb0
  have ea : algebraMap 𝒪 K a = algebraMap 𝒪 K π ^ i * algebraMap 𝒪 K ((ua⁻¹ : 𝒪ˣ) : 𝒪) := by
    rw [← map_pow, ← map_mul, ← hua, mul_assoc, Units.mul_inv, mul_one]
  have eb : algebraMap 𝒪 K b = algebraMap 𝒪 K π ^ j * algebraMap 𝒪 K ((ub⁻¹ : 𝒪ˣ) : 𝒪) := by
    rw [← map_pow, ← map_mul, ← hub, mul_assoc, Units.mul_inv, mul_one]
  have hub1 : algebraMap 𝒪 K (ub : 𝒪) * algebraMap 𝒪 K ((ub⁻¹ : 𝒪ˣ) : 𝒪) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← hx, div_eq_iff hbK, zpow_sub₀ hπK, zpow_natCast, zpow_natCast, ea, eb, Units.val_mul, map_mul]
  field_simp
  linear_combination (-1 : K) * hub1

theorem val_det_scalarGL {K : Type} [Field K] (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (scalarGL c) : Kˣ) : K) = (c : K) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]

end E33TE

open E33TE in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (∃ (c : Kˣ) (Q' : DrinfeldDatum (K := K) π B), Q.IsTranslateEven g c Q') ∨
    (∃ (c₀ c₁ : Kˣ) (Q' : DrinfeldDatum (K := K) π B), Q.IsTranslateOdd g c₀ c₁ Q') := by
  have hπK : algebraMap 𝒪 K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr hπ.ne_zero
  set p : Kˣ := Units.mk0 (algebraMap 𝒪 K π) hπK with hp
  have hpK : (p : K) = algebraMap 𝒪 K π := rfl
  obtain ⟨n, w, hw⟩ := exists_eq_unit_mul_zpow hπ (Matrix.GeneralLinearGroup.det g)
  have hwK : algebraMap 𝒪 K (w : 𝒪) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr w.ne_zero
  have hwinv : algebraMap 𝒪 K ((w⁻¹ : 𝒪ˣ) : 𝒪) = (algebraMap 𝒪 K (w : 𝒪))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left; rw [← map_mul, Units.inv_mul, map_one]

  have hdet : ∀ c : Kˣ, ((Matrix.GeneralLinearGroup.det (scalarGL c * g⁻¹) : Kˣ) : K) =
      (c : K) ^ 2 * (algebraMap 𝒪 K (w : 𝒪) * algebraMap 𝒪 K π ^ n)⁻¹ := by
    intro c
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, val_det_scalarGL, hw]
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  ·
    left
    refine ⟨p ^ k, ?_⟩
    obtain ⟨Q', hQ'⟩ := DrinfeldDatum.exists_isTranslateEven_of_det_eq_algebraMap Q g (p ^ k) w⁻¹ (by
      rw [hdet, hwinv, Units.val_zpow_eq_zpow_val, hpK, hk, two_mul, zpow_add₀ hπK]
      field_simp)
    exact ⟨Q', hQ'⟩
  ·
    right
    refine ⟨p ^ (k + 1), p ^ k, ?_⟩
    obtain ⟨Q', hQ'⟩ := DrinfeldDatum.exists_isTranslateOdd_of_det_mul_eq_algebraMap Q g (p ^ (k + 1)) (p ^ k) w⁻¹
      (by rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, hpK, zpow_add_one₀ hπK, mul_comm])
      (by
        rw [hdet, hwinv, Units.val_zpow_eq_zpow_val, hpK, hk, two_mul, zpow_add_one₀ hπK, zpow_add₀ hπK]
        field_simp)
    exact ⟨Q', hQ'⟩

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_or_exists_isTranslateOdd
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_or_exists_isTranslateOdd (solution)
