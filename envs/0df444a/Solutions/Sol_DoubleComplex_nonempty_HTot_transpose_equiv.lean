-- Prove2me | solution 1 for DoubleComplex.nonempty_HTot_transpose_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/82d9b8d1-9be6-5a81-8e34-ae91639aa6a4

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_nonempty_HTot_transpose_equiv

set_option autoImplicit false

universe u

namespace G0SOL

open DoubleComplex

variable {R : Type u} [CommRing R]

theorem neg_one_pow_eq_of_even_add {a b : ℕ} (h : Even (a + b)) : ((-1 : ℤ) ^ a) = (-1) ^ b := by
  obtain ⟨k, hk⟩ := h
  have : ((-1 : ℤ) ^ a) * (-1) ^ b = 1 := by
    rw [← pow_add, hk, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc ((-1 : ℤ) ^ a) = (-1) ^ a * ((-1) ^ b * (-1) ^ b) := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
    _ = ((-1) ^ a * (-1) ^ b) * (-1) ^ b := by rw [mul_assoc]
    _ = (-1) ^ b := by rw [this, one_mul]

theorem key_succ_succ (D : DoubleComplex.Bounded R) (p' q' : ℕ) (x₁ : D.C p' (q' + 1)) (x₂ : D.C (p' + 1) q') :
    D.dH p' (q' + 1) (((-1 : ℤ) ^ (p' * (q' + 1))) • x₁) +
        ((-1 : ℤ) ^ (p' + 1)) • D.dV (p' + 1) q' (((-1 : ℤ) ^ ((p' + 1) * q')) • x₂) =
      ((-1 : ℤ) ^ ((p' + 1) * (q' + 1))) •
        (D.dV (p' + 1) q' x₂ + ((-1 : ℤ) ^ (q' + 1)) • D.dH p' (q' + 1) x₁) := by
  have h1 : ((-1 : ℤ) ^ (p' * (q' + 1))) = (-1) ^ ((p' + 1) * (q' + 1)) * (-1) ^ (q' + 1) := by
    rw [← pow_add]; exact neg_one_pow_eq_of_even_add ⟨p' * (q' + 1) + (q' + 1), by ring⟩
  have h2 : ((-1 : ℤ) ^ (p' + 1)) * (-1) ^ ((p' + 1) * q') = (-1) ^ ((p' + 1) * (q' + 1)) := by
    rw [← pow_add]; exact neg_one_pow_eq_of_even_add ⟨(p' + 1) * (q' + 1), by ring⟩
  rw [map_zsmul, map_zsmul, smul_smul, smul_add, smul_smul, h1, h2]
  exact add_comm _ _

theorem main
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R) (n : ℕ) :
    Nonempty (DoubleComplex.HTot (DoubleComplex.transpose D) n ≃ₗ[R] DoubleComplex.HTot D n) := by
  classical

  have hswap : ∀ (p q : ℕ) (M : Type u) [AddCommGroup M] (x : M),
      ((-1 : ℤ) ^ (p * q)) • (((-1 : ℤ) ^ (q * p)) • x) = x := by
    intro p q M _ x
    rw [smul_smul, ← pow_add, mul_comm q p, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  let T : ∀ m : ℕ, Tot (transpose D) m ≃ₗ[R] Tot D m := fun m =>
    { toFun := fun c i => ((-1 : ℤ) ^ (i.1.1 * i.1.2)) •
        (c ⟨(i.1.2, i.1.1), by have := i.2; dsimp only at this ⊢; omega⟩ : D.C i.1.1 i.1.2)
      invFun := fun c i => ((-1 : ℤ) ^ (i.1.1 * i.1.2)) •
        (c ⟨(i.1.2, i.1.1), by have := i.2; dsimp only at this ⊢; omega⟩ : (transpose D).C i.1.1 i.1.2)
      map_add' := fun c c' => by
        funext i
        simp only [Pi.add_apply]
        exact smul_add _ _ _
      map_smul' := fun r c => by
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _
      left_inv := fun c => by
        funext i
        obtain ⟨⟨p, q⟩, h⟩ := i
        exact hswap p q _ _
      right_inv := fun c => by
        funext i
        obtain ⟨⟨p, q⟩, h⟩ := i
        exact hswap p q _ _ }
  have hTapp : ∀ (m : ℕ) (c : Tot (transpose D) m) (p q : ℕ) (h : p + q = m),
      T m c ⟨(p, q), h⟩ = ((-1 : ℤ) ^ (p * q)) • (c ⟨(q, p), by omega⟩ : D.C p q) :=
    fun m c p q h => rfl

  have hT : ∀ (m : ℕ) (c : Tot (transpose D) m), dTot D m (T m c) = T (m + 1) (dTot (transpose D) m c) := by
    intro m c
    funext i
    obtain ⟨⟨pp, qq⟩, h⟩ := i
    rw [hTapp]
    match pp, qq, h with
    | 0, 0, h => exact absurd h (by omega)
    | 0, q' + 1, h =>
      rw [dTot_apply_zero_succ, dTot_apply_succ_zero, hTapp, zero_mul, zero_mul, pow_zero, one_smul,
        one_smul]
      rfl
    | p' + 1, 0, h =>
      rw [dTot_apply_succ_zero, dTot_apply_zero_succ, hTapp, mul_zero, mul_zero, pow_zero, one_smul,
        one_smul]
      rfl
    | p' + 1, q' + 1, h =>
      rw [dTot_apply_succ_succ, dTot_apply_succ_succ, hTapp, hTapp]
      exact key_succ_succ D p' q' _ _

  have hmapker : ∀ m : ℕ, (LinearMap.ker (dTot (transpose D) m)).map (T m : Tot (transpose D) m →ₗ[R] Tot D m) =
      LinearMap.ker (dTot D m) := by
    intro m
    ext y
    rw [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [LinearMap.mem_ker] at hc
      rw [LinearEquiv.coe_coe, hT, hc, map_zero]
    · intro hy
      refine ⟨(T m).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
      rw [LinearMap.mem_ker]
      apply (T (m + 1)).injective
      rw [← hT, LinearEquiv.apply_symm_apply, hy, map_zero]
  let K : ∀ m : ℕ, LinearMap.ker (dTot (transpose D) m) ≃ₗ[R] LinearMap.ker (dTot D m) := fun m =>
    LinearEquiv.ofSubmodules (T m) _ _ (hmapker m)
  have hKval : ∀ (m : ℕ) (x : LinearMap.ker (dTot (transpose D) m)),
      ((K m x : LinearMap.ker (dTot D m)) : Tot D m) = T m (x : Tot (transpose D) m) := fun m x => rfl
  have hmapB : (HTotB (transpose D) n).map
      (K n : LinearMap.ker (dTot (transpose D) n) →ₗ[R] LinearMap.ker (dTot D n)) = HTotB D n := by
    match n with
    | 0 => exact Submodule.map_bot _
    | n' + 1 =>
      ext y
      simp only [HTotB, Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.mem_range]
      constructor
      · rintro ⟨x, ⟨c, hc⟩, rfl⟩
        refine ⟨T n' c, ?_⟩
        rw [LinearEquiv.coe_coe, hKval, ← hc, hT]
      · rintro ⟨c', hc'⟩
        have hx : T (n' + 1) (dTot (transpose D) n' ((T n').symm c')) = (y : Tot D (n' + 1)) := by
          rw [← hT, LinearEquiv.apply_symm_apply, hc']
        refine ⟨⟨dTot (transpose D) n' ((T n').symm c'), ?_⟩, ⟨(T n').symm c', rfl⟩, ?_⟩
        · rw [LinearMap.mem_ker, ← LinearMap.comp_apply, dTot_comp_dTot, LinearMap.zero_apply]
        · apply Subtype.ext
          rw [LinearEquiv.coe_coe, hKval]
          exact hx
  exact ⟨Submodule.Quotient.equiv (HTotB (transpose D) n) (HTotB D n) (K n) hmapB⟩

end G0SOL

theorem solution
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R) (n : ℕ) :
    Nonempty (DoubleComplex.HTot (DoubleComplex.transpose D) n ≃ₗ[R] DoubleComplex.HTot D n) :=
  G0SOL.main D n

end S_DoubleComplex_nonempty_HTot_transpose_equiv
end P2MW
export P2MW.S_DoubleComplex_nonempty_HTot_transpose_equiv (solution)
