-- Prove2me | solution 1 for BeckFialaMatrix.exists_null_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:56:04.14681+00:00
-- url     : https://prove2.me/submissions/ae835722-7e15-4239-8e32-8f28b9e8ac2f

module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_BeckFialaMatrix_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution (A : Fin m → Fin N → ℤ) (F : Finset (Fin N)) (T : Finset (Fin m))
    (hcard : T.card < F.card) :
    ∃ v : Fin N → ℚ, (∀ i ∉ F, v i = 0) ∧ (∃ i ∈ F, v i ≠ 0) ∧
      ∀ j ∈ T, ∑ i, (A j i : ℚ) * v i = 0 := by
  classical
  -- the linear map `ℚ^F → ℚ^T` given by the tight rows of `A`
  let L : ({i // i ∈ F} → ℚ) →ₗ[ℚ] ({j // j ∈ T} → ℚ) :=
    { toFun := fun w j => ∑ i : {i // i ∈ F}, (A j.1 i.1 : ℚ) * w i
      map_add' := by
        intro w1 w2; funext j
        simp only [Pi.add_apply, mul_add]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro c w; funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  -- since `#T < #F`, `L` cannot be injective
  have hninj : ¬ Function.Injective L := by
    intro hinj
    have h1 := LinearMap.finrank_le_finrank_of_injective (f := L) hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h1
    simp only [Fintype.card_coe] at h1
    omega
  obtain ⟨w1, w2, hEq, hne⟩ := Function.not_injective_iff.mp hninj
  refine ⟨fun i => if h : i ∈ F then (w1 - w2) ⟨i, h⟩ else 0, ?_, ?_, ?_⟩
  · intro i hi; simp [hi]
  · have hwne : w1 - w2 ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hwne
    exact ⟨i0.1, i0.2, by simpa using hi0⟩
  · intro j hj
    have hw0 : L (w1 - w2) = 0 := by rw [map_sub, hEq, sub_self]
    have hzero := congrFun hw0 ⟨j, hj⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hzero
    calc ∑ i, (A j i : ℚ) * (if h : i ∈ F then (w1 - w2) ⟨i, h⟩ else 0)
        = ∑ i ∈ F, (A j i : ℚ) * (if h : i ∈ F then (w1 - w2) ⟨i, h⟩ else 0) :=
          (Finset.sum_subset (Finset.subset_univ F) (by intro i _ hi; simp [hi])).symm
      _ = ∑ i ∈ F.attach, (A j i.1 : ℚ) * (w1 - w2) i := by
          rw [← Finset.sum_attach F
            (fun i => (A j i : ℚ) * (if h : i ∈ F then (w1 - w2) ⟨i, h⟩ else 0))]
          exact Finset.sum_congr rfl (fun i _ => by simp [i.2])
      _ = 0 := hzero
end BeckFialaMatrix
