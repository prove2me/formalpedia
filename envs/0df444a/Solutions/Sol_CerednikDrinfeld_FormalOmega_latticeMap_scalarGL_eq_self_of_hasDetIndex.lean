-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.latticeMap_scalarGL_eq_self_of_hasDetIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8a90bf44-a649-523f-87cf-7402036efa7f

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_latticeMap_scalarGL_eq_self_of_hasDetIndex

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace R4CDMDetIndex

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

theorem latticeMap_scalarGL_stdLattice_of_isUnit (a : 𝒪) (ha : IsUnit a) (c : Kˣ)
    (hc : algebraMap 𝒪 K a = (c : K)) :
    latticeMap (scalarGL c) (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
  obtain ⟨b, hab⟩ := ha.exists_right_inv
  have hcinv : ((c⁻¹ : Kˣ) : K) = algebraMap 𝒪 K b := by
    have h1 : (c : K) * algebraMap 𝒪 K b = 1 := by
      rw [← hc, ← map_mul, hab, map_one]
    calc ((c⁻¹ : Kˣ) : K) = ((c⁻¹ : Kˣ) : K) * ((c : K) * algebraMap 𝒪 K b) := by rw [h1, mul_one]
      _ = algebraMap 𝒪 K b := by rw [← mul_assoc, Units.inv_mul, one_mul]
  apply le_antisymm
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [mem_stdLattice] at hw ⊢
    intro i
    rw [Pi.smul_apply, smul_eq_mul, ← hc]
    obtain ⟨y, hy⟩ := hw i
    exact ⟨a * y, by rw [map_mul, hy]⟩
  · intro v hv
    rw [mem_stdLattice] at hv
    refine mem_latticeMap_scalarGL.mpr ⟨((c⁻¹ : Kˣ) : K) • v, ?_, ?_⟩
    · rw [mem_stdLattice]
      intro i
      rw [Pi.smul_apply, smul_eq_mul, hcinv]
      obtain ⟨y, hy⟩ := hv i
      exact ⟨b * y, by rw [map_mul, hy]⟩
    · rw [smul_smul, Units.mul_inv, one_smul]

theorem det_scalarGL (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (scalarGL c) : Kˣ) : K) = (c : K) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]

end R4CDMDetIndex

open R4CDMDetIndex in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (N : Submodule 𝒪 (Fin 2 → K)) (c : Kˣ) (e : ℤ)
    (h : HasDetIndex π N e) (h' : HasDetIndex π (latticeMap (scalarGL c) N) e) : latticeMap (scalarGL c) N = N := by
  obtain ⟨g, hg, u, hu⟩ := h
  obtain ⟨g', hg', u', hu'⟩ := h'
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h0 => hπ.ne_zero (hinj (by rw [h0, map_zero]))

  have hfix : latticeMap (g'⁻¹ * (scalarGL c * g)) (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
    rw [latticeMap_mul, latticeMap_mul, hg, ← hg', latticeMap_inv_latticeMap]
  obtain ⟨k, hk⟩ := (latticeMap_stdLattice_eq_iff_mem_range _).mp hfix

  have hdet : algebraMap 𝒪 K ((Matrix.GeneralLinearGroup.det k : 𝒪ˣ) : 𝒪) *
      ((Matrix.GeneralLinearGroup.det g' : Kˣ) : K) =
      (c : K) ^ 2 * ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) := by
    have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) k) =
        Matrix.GeneralLinearGroup.det (g'⁻¹ * (scalarGL c * g)) := by rw [hk]
    rw [Matrix.GeneralLinearGroup.map_det, map_mul, map_mul, map_inv] at h1
    have h2 := congrArg (fun x : Kˣ => ((Matrix.GeneralLinearGroup.det g' * x : Kˣ) : K)) h1
    rw [← mul_assoc, mul_inv_cancel, one_mul, Units.val_mul, Units.val_mul, Units.coe_map, det_scalarGL] at h2
    rw [mul_comm]
    exact h2

  set w : 𝒪ˣ := Matrix.GeneralLinearGroup.det k * u' * u⁻¹ with hw
  have hc2 : (c : K) ^ 2 = algebraMap 𝒪 K ((w : 𝒪ˣ) : 𝒪) := by
    have hπe : (algebraMap 𝒪 K π) ^ e ≠ 0 := zpow_ne_zero e hπK
    have hug : ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) ≠ 0 := Units.ne_zero _
    rw [hu', hu] at hdet

    have huK : algebraMap 𝒪 K ((u : 𝒪ˣ) : 𝒪) ≠ 0 := by
      intro h0; exact (u.isUnit.map (algebraMap 𝒪 K)).ne_zero h0
    have key : (c : K) ^ 2 * algebraMap 𝒪 K ((u : 𝒪ˣ) : 𝒪) =
        algebraMap 𝒪 K ((Matrix.GeneralLinearGroup.det k : 𝒪ˣ) : 𝒪) * algebraMap 𝒪 K ((u' : 𝒪ˣ) : 𝒪) := by
      apply mul_right_cancel₀ hπe
      rw [mul_assoc, mul_assoc]; exact hdet.symm
    have hwval : ((w : 𝒪ˣ) : 𝒪) * ((u : 𝒪ˣ) : 𝒪) =
        ((Matrix.GeneralLinearGroup.det k : 𝒪ˣ) : 𝒪) * ((u' : 𝒪ˣ) : 𝒪) := by
      rw [hw, Units.val_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    apply mul_right_cancel₀ huK
    rw [key, ← map_mul, ← map_mul, hwval]

  obtain ⟨a, ha⟩ : ∃ a : 𝒪, algebraMap 𝒪 K a = (c : K) := by
    refine IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (n := 2) (by norm_num) ?_
    rw [hc2]; exact isIntegral_algebraMap
  have haunit : IsUnit a := by
    have h2 : a * a = ((w : 𝒪ˣ) : 𝒪) := hinj (by rw [map_mul, ha, ← sq, hc2])
    exact isUnit_of_mul_isUnit_left (h2 ▸ w.isUnit)

  have hstd : latticeMap (scalarGL c) (stdLattice 𝒪 K) = stdLattice 𝒪 K :=
    latticeMap_scalarGL_stdLattice_of_isUnit a haunit c ha
  calc latticeMap (scalarGL c) N = latticeMap (scalarGL c * g) (stdLattice 𝒪 K) := by rw [latticeMap_mul, hg]
    _ = latticeMap (g * scalarGL c) (stdLattice 𝒪 K) := by rw [scalarGL_mul_comm]
    _ = N := by rw [latticeMap_mul, hstd, hg]

end S_CerednikDrinfeld_FormalOmega_latticeMap_scalarGL_eq_self_of_hasDetIndex
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_latticeMap_scalarGL_eq_self_of_hasDetIndex (solution)
