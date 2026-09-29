-- Prove2me | solution 1 for Deformation.convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/90c639a0-041f-5129-8875-790df5d373f4

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_Deformation_convPow_prime_apply_coeff_of_mem_wittHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

noncomputable section

open Function
open scoped TensorProduct

namespace UnipotentOfWittEmbedding

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {A : Type v} [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]

theorem toDual_pow (φ : CartierDual k A) (N : ℕ) :
    CartierDual.toDual k A (φ ^ N) = (WithConv.toConv (CartierDual.toDual k A φ) ^ N).ofConv := by
  induction N with
  | zero =>
    rw [pow_zero, pow_zero, CartierDual.one_def, CartierDual.toDual_ofDual,
      CartierDual.convOne_ofConv_eq_counit]
  | succ N ih =>
    rw [pow_succ, pow_succ, CartierDual.mul_eq_convMul, ih, WithConv.toConv_ofConv]

theorem pow_apply_eq_convPow (φ : CartierDual k A) (N : ℕ) (a : A) :
    (φ ^ N) a = (WithConv.toConv (CartierDual.toDual k A φ) ^ N).ofConv a := by
  rw [← toDual_pow]; rfl

theorem mul_apply_one (φ ψ : CartierDual k A) : (φ * ψ) 1 = φ 1 * ψ 1 := by
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply]
  rfl

theorem pow_apply_one (φ : CartierDual k A) (N : ℕ) : (φ ^ N) 1 = φ 1 ^ N := by
  induction N with
  | zero => rw [pow_zero, pow_zero, CartierDual.one_apply, Bialgebra.counit_one]
  | succ N ih => rw [pow_succ, pow_succ, mul_apply_one, ih]

theorem convPow_apply_coeff_eq_zero {n : ℕ} {x : TruncatedWittVector p n A} (hx : x ∈ Deformation.wittHom k p n A)
    (β : WithConv (A →ₗ[k] k)) (m : ℕ) (i : Fin n) (him : (i : ℕ) < m) :
    (β ^ p ^ m).ofConv (x.coeff i) = 0 := by
  induction m generalizing β i with
  | zero => exact absurd him (Nat.not_lt_zero _)
  | succ m ih =>
    have hkey := Deformation.convPow_prime_apply_coeff_of_mem_wittHom k p A k (β ^ p ^ m) hx
    rw [pow_succ, pow_mul]
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => exact hkey.1 hi
    | succ i' =>
      rw [hkey.2 i' hi, ih β ⟨i', Nat.lt_of_succ_lt hi⟩ (by simpa using him), zero_pow hp.out.ne_zero]

theorem pow_apply_coeff_eq_zero {n : ℕ} {x : TruncatedWittVector p n A} (hx : x ∈ Deformation.wittHom k p n A)
    (φ : CartierDual k A) (i : Fin n) : (φ ^ p ^ n) (x.coeff i) = 0 := by
  rw [pow_apply_eq_convPow]
  exact convPow_apply_coeff_eq_zero hx _ n i i.isLt

scoped instance nontrivial_cartierDual : Nontrivial (CartierDual k A) :=
  ⟨⟨0, 1, fun h => by
    have h1 := congrArg (fun χ : CartierDual k A => χ 1) h
    simp only [CartierDual.one_apply, Bialgebra.counit_one] at h1
    exact zero_ne_one h1⟩⟩

scoped instance nontrivial_tensor : Nontrivial (CartierDual k A ⊗[k] CartierDual k A) :=
  RingHom.domain_nontrivial (Algebra.TensorProduct.lmul' k (S := CartierDual k A)).toRingHom

scoped instance charP_tensor : CharP (CartierDual k A ⊗[k] CartierDual k A) p :=
  charP_of_injective_algebraMap (algebraMap k (CartierDual k A ⊗[k] CartierDual k A)).injective p

variable (k A) in

def pairing (t : A ⊗[k] A) : (CartierDual k A ⊗[k] CartierDual k A) →ₗ[k] k :=
  (LinearMap.applyₗ t).comp ((TensorProduct.dualDistrib k A A).comp
    (TensorProduct.map (CartierDual.toDual k A).toLinearMap (CartierDual.toDual k A).toLinearMap))

theorem pairing_apply (t : A ⊗[k] A) (w : CartierDual k A ⊗[k] CartierDual k A) :
    pairing k A t w = TensorProduct.dualDistrib k A A
      (TensorProduct.map (CartierDual.toDual k A).toLinearMap (CartierDual.toDual k A).toLinearMap w) t := rfl

theorem pairing_tmul_tmul (a b : A) (x y : CartierDual k A) :
    pairing k A (a ⊗ₜ[k] b) (x ⊗ₜ[k] y) = x a * y b := by
  rw [pairing_apply, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
  rfl

theorem pairing_comul (a b : A) (φ : CartierDual k A) :
    pairing k A (a ⊗ₜ[k] b) (Coalgebra.comul (R := k) φ) = φ (a * b) := by
  rw [pairing_apply]
  exact CartierDual.comul_pairing φ a b

theorem comul_pow_eq_sum (φ : CartierDual k A) (S : Finset (CartierDual k A × CartierDual k A))
    (hS : Coalgebra.comul (R := k) φ = ∑ i ∈ S, i.1 ⊗ₜ[k] i.2) (m : ℕ) :
    Coalgebra.comul (R := k) (φ ^ p ^ m) = ∑ i ∈ S, (i.1 ^ p ^ m) ⊗ₜ[k] (i.2 ^ p ^ m) := by
  have h : Coalgebra.comul (R := k) (φ ^ p ^ m) = (Coalgebra.comul (R := k) φ) ^ p ^ m :=
    Bialgebra.comul_pow φ (p ^ m)
  rw [h, hS]
  refine (sum_pow_char_pow p m S _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Algebra.TensorProduct.tmul_pow _ _ _

variable (k p A) in

def U (n : ℕ) : Subalgebra k A where
  carrier := {a | ∀ φ : CartierDual k A, (φ ^ p ^ n) a = φ 1 ^ p ^ n * Coalgebra.counit (R := k) a}
  mul_mem' {a b} ha hb := by
    intro φ
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := k) (Coalgebra.comul (R := k) φ)

    have ha' : ∀ φ : CartierDual k A, (φ ^ p ^ n) a = φ 1 ^ p ^ n * Coalgebra.counit (R := k) a := ha
    have hb' : ∀ φ : CartierDual k A, (φ ^ p ^ n) b = φ 1 ^ p ^ n * Coalgebra.counit (R := k) b := hb
    rw [← pairing_comul, comul_pow_eq_sum φ S hS n, map_sum]
    simp only [pairing_tmul_tmul, ha', hb']

    have h1 : φ 1 = ∑ i ∈ S, i.1 1 * i.2 1 := by
      rw [← mul_one (1 : A), ← pairing_comul, hS, map_sum]
      simp only [pairing_tmul_tmul, mul_one]
    rw [Bialgebra.counit_mul, h1, sum_pow_char_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]; ring
  one_mem' := by
    intro φ
    rw [pow_apply_one, Bialgebra.counit_one, mul_one]
  add_mem' {a b} ha hb := by
    intro φ
    rw [map_add, map_add, ha φ, hb φ, mul_add]
  zero_mem' := by
    intro φ
    rw [map_zero, map_zero, mul_zero]
  algebraMap_mem' r := by
    intro φ
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, pow_apply_one, Bialgebra.counit_one,
      smul_eq_mul, smul_eq_mul, mul_one, mul_comm]

theorem mem_U {n : ℕ} {a : A} :
    a ∈ U k p A n ↔ ∀ φ : CartierDual k A, (φ ^ p ^ n) a = φ 1 ^ p ^ n * Coalgebra.counit (R := k) a :=
  Iff.rfl

theorem coeff_mem_U {n : ℕ} {x : TruncatedWittVector p n A} (hx : x ∈ Deformation.wittHom k p n A)
    (i : Fin n) : x.coeff i ∈ U k p A n := by
  intro φ
  rw [pow_apply_coeff_eq_zero hx, Deformation.counit_coeff_of_mem_wittHom hx, mul_zero]

theorem U_eq_top (n : ℕ)
    (hgen : Algebra.adjoin k {a : A | ∃ (x : Deformation.wittHom k p n A) (i : Fin n),
      (x : TruncatedWittVector p n A).coeff i = a} = ⊤) : U k p A n = ⊤ := by
  refine top_le_iff.1 ?_
  rw [← hgen]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨x, i, rfl⟩
  exact coeff_mem_U x.2 i

theorem pow_eq_zero_of_apply_one (n : ℕ)
    (hgen : Algebra.adjoin k {a : A | ∃ (x : Deformation.wittHom k p n A) (i : Fin n),
      (x : TruncatedWittVector p n A).coeff i = a} = ⊤)
    (φ : CartierDual k A) (hφ : φ 1 = 0) : φ ^ p ^ n = 0 := by
  refine CartierDual.ext fun a => ?_
  have ha : a ∈ U k p A n := by rw [U_eq_top n hgen]; trivial
  rw [ha φ, hφ, zero_pow (pow_ne_zero _ hp.out.ne_zero), zero_mul]
  rfl

theorem convPow_eq_zero (n : ℕ)
    (hgen : Algebra.adjoin k {a : A | ∃ (x : Deformation.wittHom k p n A) (i : Fin n),
      (x : TruncatedWittVector p n A).coeff i = a} = ⊤)
    (β : WithConv (A →ₗ[k] k)) (hβ : β.ofConv 1 = 0) : β ^ p ^ n = 0 := by
  have h := pow_eq_zero_of_apply_one n hgen (CartierDual.ofDual k A β.ofConv) hβ
  have h2 := toDual_pow (CartierDual.ofDual k A β.ofConv) (p ^ n)
  rw [h, CartierDual.toDual_ofDual, WithConv.toConv_ofConv] at h2

  have h3 : (β ^ p ^ n).ofConv = 0 := h2.symm
  exact WithConv.ofConv_injective h3

theorem isLocalRing (n : ℕ)
    (hgen : Algebra.adjoin k {a : A | ∃ (x : Deformation.wittHom k p n A) (i : Fin n),
      (x : TruncatedWittVector p n A).coeff i = a} = ⊤) : IsLocalRing (CartierDual k A) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun φ => ?_

  set c : k := φ 1 with hc
  have hψ : IsNilpotent (φ - algebraMap k (CartierDual k A) c) := by
    refine ⟨p ^ n, pow_eq_zero_of_apply_one n hgen _ ?_⟩
    change φ 1 - algebraMap k (CartierDual k A) c 1 = 0
    rw [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul, hc, sub_self]
  by_cases h0 : c = 0
  · right
    have h1 : IsNilpotent φ := by rwa [h0, map_zero, sub_zero] at hψ
    exact h1.isUnit_one_sub
  · left
    have hu : IsUnit (algebraMap k (CartierDual k A) c) := (Ne.isUnit h0).map _
    have := hψ.isUnit_add_left_of_commute hu (Commute.all _ _)
    rwa [add_sub_cancel] at this

end UnipotentOfWittEmbedding
p2m_reactivate "P2MW.S_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top.UnipotentOfWittEmbedding"

end
p2m_reactivate "P2MW.S_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top.UnipotentOfWittEmbedding"

theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (hgen : Algebra.adjoin k {a : A | ∃ (x : Deformation.wittHom k p n A) (i : Fin n),
      (x : TruncatedWittVector p n A).coeff i = a} = ⊤) :
    (∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0) ∧
      IsLocalRing (CartierDual k A) :=
  ⟨fun β hβ => UnipotentOfWittEmbedding.convPow_eq_zero n hgen β hβ,
    UnipotentOfWittEmbedding.isLocalRing n hgen⟩

end S_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top
end P2MW
export P2MW.S_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top (solution)
