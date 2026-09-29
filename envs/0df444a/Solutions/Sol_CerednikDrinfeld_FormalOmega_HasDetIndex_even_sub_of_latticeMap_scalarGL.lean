-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c3266a26-5a48-52b2-803c-fc67816a5fc4

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_HasDetIndex_even_sub_of_latticeMap_scalarGL

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B24IH

theorem exists_unit_mul_zpow_of_ne_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : 𝒪ˣ), x = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx (by rw [map_zero, zero_div])
  obtain ⟨i, ua, hua⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hπ
  obtain ⟨j, ub, hub⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ

  refine ⟨(i : ℤ) - j, ua⁻¹ * ub, ?_⟩
  have ha : algebraMap 𝒪 K a = algebraMap 𝒪 K π ^ i * algebraMap 𝒪 K (ua⁻¹ : 𝒪ˣ) := by
    rw [← map_pow, ← hua, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hb' : algebraMap 𝒪 K b = algebraMap 𝒪 K π ^ j * algebraMap 𝒪 K (ub⁻¹ : 𝒪ˣ) := by
    rw [← map_pow, ← hub, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hubK : algebraMap 𝒪 K (ub : 𝒪ˣ) ≠ 0 := by
    intro h
    apply ub.ne_zero
    exact IsFractionRing.injective 𝒪 K (by rw [h, map_zero])
  have hBi : algebraMap 𝒪 K (ub⁻¹ : 𝒪ˣ) = (algebraMap 𝒪 K (ub : 𝒪ˣ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [ha, hb', hBi, zpow_sub₀ hπK, zpow_natCast, zpow_natCast, Units.val_mul, map_mul]
  field_simp

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

theorem val_det_scalarGL (a : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (scalarGL a) : Kˣ) : K) = (a : K) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]

variable [IsFractionRing 𝒪 K]

theorem zpow_eq_algebraMap_unit {π : 𝒪} (hπ : Irreducible π) (m : ℤ) (u : 𝒪ˣ)
    (h : algebraMap 𝒪 K π ^ m = algebraMap 𝒪 K u) : m = 0 := by
  have hinj := IsFractionRing.injective 𝒪 K
  have key : ∀ n : ℕ, IsUnit (π ^ n) → n = 0 := fun n hn => by
    by_contra h0
    exact hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π h0) hn)
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, ← map_pow] at h
    have := key n (hinj h ▸ u.isUnit)
    simp [this]
  · have hu0 : algebraMap 𝒪 K u ≠ 0 := fun h0 => u.ne_zero (hinj (by rw [h0, map_zero]))
    rw [zpow_neg, zpow_natCast, ← map_pow, inv_eq_iff_eq_inv] at h
    have h1 : algebraMap 𝒪 K (π ^ n * u) = algebraMap 𝒪 K 1 := by
      rw [map_mul, h, inv_mul_cancel₀ hu0, map_one]
    have := key n (IsUnit.of_mul_eq_one _ (hinj h1))
    simp [this]

theorem zpow_exp_unique {π : 𝒪} (hπ : Irreducible π) (a b : ℤ) (w₁ w₂ : 𝒪ˣ)
    (h : algebraMap 𝒪 K w₁ * algebraMap 𝒪 K π ^ a = algebraMap 𝒪 K w₂ * algebraMap 𝒪 K π ^ b) : a = b := by
  have hinj := IsFractionRing.injective 𝒪 K
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h0 => hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have hw1 : algebraMap 𝒪 K w₁ ≠ 0 := fun h0 => w₁.ne_zero (hinj (by rw [h0, map_zero]))
  have key : algebraMap 𝒪 K π ^ (a - b) = algebraMap 𝒪 K ((w₂ * w₁⁻¹ : 𝒪ˣ)) := by
    rw [zpow_sub₀ hπK, div_eq_iff (zpow_ne_zero _ hπK), Units.val_mul, map_mul, map_units_inv,
      mul_assoc, mul_comm ((algebraMap 𝒪 K ↑w₁)⁻¹), ← mul_assoc, ← h]
    field_simp
  have := zpow_eq_algebraMap_unit hπ _ _ key
  omega

end B24IH

open B24IH in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (N : Submodule 𝒪 (Fin 2 → K)) (c : Kˣ) (e e' : ℤ)
    (h : HasDetIndex π N e) (h' : HasDetIndex π (latticeMap (scalarGL c) N) e') : Even (e - e') := by
  obtain ⟨g, hg, u, hu⟩ := h
  obtain ⟨g', hg', u', hu'⟩ := h'

  have hfix : latticeMap ((scalarGL c * g)⁻¹ * g') (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
    rw [latticeMap_mul, hg', ← hg, ← latticeMap_mul, ← latticeMap_mul, mul_assoc, inv_mul_cancel, latticeMap_one]
  obtain ⟨M, hM⟩ := (latticeMap_stdLattice_eq_iff_mem_range _).mp hfix

  have hdet : (Matrix.GeneralLinearGroup.det g' : Kˣ) =
      Matrix.GeneralLinearGroup.det (scalarGL c) * Matrix.GeneralLinearGroup.det g *
        Matrix.GeneralLinearGroup.det ((scalarGL c * g)⁻¹ * g') := by
    conv_lhs => rw [← mul_inv_cancel_left (scalarGL c * g) g']
    rw [map_mul, map_mul]
  have hdetk : ((Matrix.GeneralLinearGroup.det ((scalarGL c * g)⁻¹ * g') : Kˣ) : K) =
      algebraMap 𝒪 K (Matrix.GeneralLinearGroup.det M : 𝒪ˣ) := by
    rw [← hM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    show ((M : Matrix (Fin 2) (Fin 2) 𝒪).map (algebraMap 𝒪 K)).det = _
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  obtain ⟨n, v, hv⟩ := exists_unit_mul_zpow_of_ne_zero hπ hc0
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h0 => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h0, map_zero]))

  have heq : algebraMap 𝒪 K u' * algebraMap 𝒪 K π ^ e' =
      (algebraMap 𝒪 K v * algebraMap 𝒪 K π ^ n) ^ 2 * (algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ e) *
        algebraMap 𝒪 K (Matrix.GeneralLinearGroup.det M : 𝒪ˣ) := by
    rw [← hu', ← hv, ← val_det_scalarGL, ← hu, ← hdetk, hdet, Units.val_mul, Units.val_mul]
  have heq' : algebraMap 𝒪 K u' * algebraMap 𝒪 K π ^ e' =
      algebraMap 𝒪 K ((v * v * u * Matrix.GeneralLinearGroup.det M : 𝒪ˣ)) * algebraMap 𝒪 K π ^ (2 * n + e) := by
    rw [heq, zpow_add₀ hπK, two_mul, zpow_add₀ hπK, Units.val_mul, Units.val_mul, Units.val_mul, map_mul, map_mul,
      map_mul]
    ring
  have := zpow_exp_unique hπ _ _ _ _ heq'
  exact ⟨-n, by omega⟩

end S_CerednikDrinfeld_FormalOmega_HasDetIndex_even_sub_of_latticeMap_scalarGL
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_HasDetIndex_even_sub_of_latticeMap_scalarGL (solution)
