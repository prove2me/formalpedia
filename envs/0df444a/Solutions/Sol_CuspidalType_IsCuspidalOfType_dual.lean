-- Prove2me | solution 1 for CuspidalType.IsCuspidalOfType.dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fa427383-a9a5-5e8c-b245-a260ccb3ebb7

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_IsCuspidalOfType_dual

set_option autoImplicit false

open Polynomial

namespace Ws41
namespace CuspDual

section LinAlg

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem _root_.Ws41.CuspDual.charpoly_transpose [FiniteDimensional K V] (f : V →ₗ[K] V) :
    (Module.Dual.transpose (R := K) f).charpoly = f.charpoly := by
  classical
  let b := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix (Module.Dual.transpose (R := K) f) b.dualBasis,
    LinearMap.toMatrix_transpose, Matrix.charpoly_transpose, LinearMap.charpoly_toMatrix]

p2m_export "Ws41.CuspDual" "charpoly_transpose"

theorem transpose_id : Module.Dual.transpose (R := K) (LinearMap.id : V →ₗ[K] V) = LinearMap.id := by
  ext f v
  simp [Module.Dual.transpose_apply]

end LinAlg

section Perm

variable {k G H : Type*} [Field k] [Group G] [MulAction G H] [Finite H]

theorem charpoly_ofMulAction_inv (g : G) :
    (Representation.ofMulActionFinsupp k G H g⁻¹).charpoly = (Representation.ofMulActionFinsupp k G H g).charpoly := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let b : Module.Basis H k (H →₀ k) := Finsupp.basisSingleOne
  rw [← LinearMap.charpoly_toMatrix _ b, ← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, b, Finsupp.coe_basisSingleOne,
    Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Representation.ofMulActionFinsupp_single,
    Finsupp.single_apply, inv_smul_eq_iff]
  by_cases hij : i = g • j
  · rw [if_pos hij, if_pos hij.symm]
  · rw [if_neg hij, if_neg (Ne.symm hij)]

end Perm

section Unipotent

open CuspidalType

variable {q : ℕ} [Fact q.Prime]

theorem unipotent_mul (s t : ZMod q) : unipotent q s * unipotent q t = unipotent q (s + t) := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_inv (t : ZMod q) : (unipotent q t)⁻¹ = unipotent q (-t) :=
  Units.ext rfl

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V}

theorem sum_unipotent_apply_eq_zero (h : IsCuspidalOfType θ ρ) (v : V) :
    (∑ t : ZMod q, ρ (unipotent q t) v) = 0 := by
  apply h.cuspidal
  intro s
  rw [map_sum]
  have : ∀ t : ZMod q, ρ (unipotent q s) (ρ (unipotent q t) v) = ρ (unipotent q (s + t)) v := by
    intro t
    rw [← unipotent_mul, map_mul, Module.End.mul_apply]
  simp_rw [this]
  exact Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun t => rfl)

theorem dual_eq_zero_of_forall_comp_unipotent [CharZero K] (h : IsCuspidalOfType θ ρ) (f : Module.Dual K V)
    (hf : ∀ t : ZMod q, f ∘ₗ ρ (unipotent q t) = f) : f = 0 := by
  ext v
  have hsum : (∑ t : ZMod q, f (ρ (unipotent q t) v)) = (q : K) • f v := by
    have hc : ∀ t : ZMod q, f (ρ (unipotent q t) v) = f v := fun t =>
      LinearMap.congr_fun (hf t) v
    simp only [hc, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, smul_eq_mul]
  have hzero : (q : K) • f v = 0 := by
    rw [← hsum, ← map_sum, sum_unipotent_apply_eq_zero h v, map_zero]
  have hq : (q : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  simpa [hq] using hzero

end Unipotent

end Ws41.CuspDual

open Ws41.CuspDual CuspidalType in
theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K] {θ : (GaloisField q 2)ˣ →* Kˣ}
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    (h : CuspidalType.IsCuspidalOfType θ ρ) :
    CuspidalType.IsCuspidalOfType θ ρ.dual := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact Subspace.dual_finrank_eq.trans h.finrank_eq
  ·
    intro f hf
    apply dual_eq_zero_of_forall_comp_unipotent h f
    intro t
    have := hf (-t)
    rw [Representation.dual_apply, unipotent_inv, neg_neg, Module.Dual.transpose_apply] at this
    exact this
  ·
    intro c
    rw [Representation.dual_apply, ← map_inv, h.central, transpose_id]
  ·
    intro α
    rw [Representation.dual_apply, charpoly_transpose]
    have key := h.torus_charpoly α⁻¹
    rw [map_inv θ, inv_inv, map_inv (torus q),
      mul_comm (X - C (((θ α)⁻¹ : Kˣ) : K)) (X - C ((θ α : Kˣ) : K))] at key
    rw [key]
    exact charpoly_ofMulAction_inv (k := K) (H := ProjLine q) (torus q α)

end S_CuspidalType_IsCuspidalOfType_dual
end P2MW
export P2MW.S_CuspidalType_IsCuspidalOfType_dual (solution)
