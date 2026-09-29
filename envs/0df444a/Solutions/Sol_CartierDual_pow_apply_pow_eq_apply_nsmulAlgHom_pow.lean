-- Prove2me | solution 1 for CartierDual.pow_apply_pow_eq_apply_nsmulAlgHom_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f470f166-a57d-5f72-a433-abe15ccba330

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open Coalgebra

namespace PDivFV

section Orbit

def Tup (ι : Type*) (p : ℕ) : Type _ := ZMod p → ι

namespace Tup

variable {ι : Type*} {p : ℕ}

scoped instance instFintype [Fintype ι] [NeZero p] : Fintype (Tup ι p) :=
  inferInstanceAs (Fintype (ZMod p → ι))

scoped instance instMulAction : MulAction (Multiplicative (ZMod p)) (Tup ι p) where
  smul r I := fun j => I (j + Multiplicative.toAdd r)
  one_smul I := funext fun j => by
    change I (j + Multiplicative.toAdd (1 : Multiplicative (ZMod p))) = I j
    rw [toAdd_one, add_zero]
  mul_smul r s I := funext fun j => by
    change I (j + Multiplicative.toAdd (r * s)) =
      I (j + Multiplicative.toAdd r + Multiplicative.toAdd s)
    rw [toAdd_mul, add_assoc]

theorem smul_apply (r : Multiplicative (ZMod p)) (I : Tup ι p) (j : ZMod p) :
    (r • I) j = I (j + Multiplicative.toAdd r) := rfl

def const (i : ι) : Tup ι p := fun _ => i

@[scoped simp] theorem const_apply (i : ι) (j : ZMod p) : (const i : Tup ι p) j = i := rfl

theorem smul_const (r : Multiplicative (ZMod p)) (i : ι) :
    (r • (const i : Tup ι p)) = const i := rfl

theorem eq_const_of_mem_fixedPoints {I : Tup ι p}
    (hI : I ∈ MulAction.fixedPoints (Multiplicative (ZMod p)) (Tup ι p)) :
    I = const (I 0) := by
  funext j
  have h := congrFun (MulAction.mem_fixedPoints.1 hI (Multiplicative.ofAdd j)) 0
  rw [smul_apply, toAdd_ofAdd, zero_add] at h
  exact h

theorem const_mem_fixedPoints (i : ι) :
    (const i : Tup ι p) ∈ MulAction.fixedPoints (Multiplicative (ZMod p)) (Tup ι p) :=
  MulAction.mem_fixedPoints.2 fun _ => rfl

theorem eq_const_of_mem_orbit_const {i : ι} {I : Tup ι p}
    (hI : I ∈ MulAction.orbit (Multiplicative (ZMod p)) (const i : Tup ι p)) :
    I = const i := by
  obtain ⟨r, rfl⟩ := MulAction.mem_orbit_iff.1 hI
  rfl

theorem sum_eq_sum_const [Fintype ι] [hp : Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (hM : ∀ m : M, p • m = 0) (g : Tup ι p → M)
    (hg : ∀ (r : Multiplicative (ZMod p)) (I : Tup ι p), g (r • I) = g I) :
    ∑ I : Tup ι p, g I = ∑ i : ι, g (const i) := by
  classical
  set G := Multiplicative (ZMod p) with hG
  have hcardG : Fintype.card G = p := by simp [G]
  letI : Fintype (MulAction.orbitRel.Quotient G (Tup ι p)) :=
    @Quotient.fintype _ _ (MulAction.orbitRel G (Tup ι p)) (fun _ _ => Classical.propDecidable _)
  let e := MulAction.selfEquivSigmaOrbits' G (Tup ι p)

  have hout : ∀ (ω : MulAction.orbitRel.Quotient G (Tup ι p)) (y : Tup ι p), y ∈ ω.orbit →
      g y = g ω.out := by
    intro ω y hy
    have hy' : y ∈ MulAction.orbit G ω.out := by
      rw [MulAction.orbitRel.Quotient.mem_orbit] at hy
      have h2 : Quotient.mk'' ω.out = ω := Quotient.out_eq' ω
      have := Quotient.exact' (hy.trans h2.symm)
      exact (MulAction.orbitRel_apply).1 this
    obtain ⟨r, rfl⟩ := MulAction.mem_orbit_iff.1 hy'
    exact hg r _

  have horb : ∀ ω : MulAction.orbitRel.Quotient G (Tup ι p),
      ω.orbit = MulAction.orbit G ω.out := fun ω =>
    MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq'

  have hsize : ∀ ω : MulAction.orbitRel.Quotient G (Tup ι p),
      Fintype.card (MulAction.orbit G ω.out) = 1 ∨ Fintype.card (MulAction.orbit G ω.out) = p := by
    intro ω
    apply hp.out.eq_one_or_self_of_dvd
    refine ⟨Fintype.card (MulAction.stabilizer G ω.out), ?_⟩
    rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group, hcardG]

  have step1 : ∑ I : Tup ι p, g I =
      ∑ ω : MulAction.orbitRel.Quotient G (Tup ι p),
        Fintype.card (MulAction.orbit G ω.out) • g ω.out := by
    rw [← Equiv.sum_comp e.symm g, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hval : ∀ y : ω.orbit, g (e.symm ⟨ω, y⟩) = g ω.out := fun y => hout ω y.1 y.2
    rw [Fintype.sum_congr _ _ hval, Finset.sum_const, Finset.card_univ]
    congr 1
    exact Fintype.card_congr (Equiv.setCongr (horb ω))

  have step2 : ∀ ω : MulAction.orbitRel.Quotient G (Tup ι p),
      Fintype.card (MulAction.orbit G ω.out) • g ω.out =
        if Fintype.card (MulAction.orbit G ω.out) = 1 then g (const (ω.out 0)) else 0 := by
    intro ω
    rcases hsize ω with h1 | hP
    · rw [if_pos h1, h1, one_smul]
      have hfix := (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).2 h1
      rw [← eq_const_of_mem_fixedPoints hfix]
    · rw [hP, hM, if_neg]
      exact hp.out.one_lt.ne'
  rw [step1, Fintype.sum_congr _ _ step2, Finset.sum_ite, Finset.sum_const_zero, add_zero]

  have hout_const : ∀ i : ι,
      (Quotient.mk'' (const i : Tup ι p) : MulAction.orbitRel.Quotient G (Tup ι p)).out =
        const i := by
    intro i
    apply eq_const_of_mem_orbit_const
    apply (MulAction.orbitRel_apply).1
    exact Quotient.exact' (Quotient.out_eq' _)
  symm
  refine Finset.sum_nbij' (fun i => (Quotient.mk'' (const i : Tup ι p)))
    (fun ω => ω.out 0) ?_ ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter, hout_const]
    exact ⟨Finset.mem_univ _,
      (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).1 (const_mem_fixedPoints i)⟩
  · intro ω _
    exact Finset.mem_univ _
  · intro i _
    change (Quotient.mk'' (const i : Tup ι p) : MulAction.orbitRel.Quotient G (Tup ι p)).out 0 = i
    rw [hout_const]
    rfl
  · intro ω hω
    rw [Finset.mem_filter] at hω
    have hfix := (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).2 hω.2
    change (Quotient.mk'' (const (ω.out 0) : Tup ι p) : MulAction.orbitRel.Quotient G (Tup ι p)) = ω
    rw [← eq_const_of_mem_fixedPoints hfix]
    exact Quotient.out_eq' ω
  · intro i _
    rw [hout_const]
    rfl

end Tup
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup"

end Orbit
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup"

end PDivFV
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV"

namespace PDivFV

section CharP

variable (p : ℕ) [hp : Fact p.Prime]

theorem add_pow_char' {T : Type*} [CommRing T] (hT : (p : T) = 0) (x y : T) :
    (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp.out, hT, zero_mul, zero_mul, zero_mul, add_zero]

theorem sum_pow_char' {T : Type*} [CommRing T] (hT : (p : T) = 0) {κ : Type*} (s : Finset κ)
    (f : κ → T) : (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, f i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow hp.out.ne_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char' p hT, ih]

theorem cast_eq_zero_of_algebraMap {R : Type*} [CommSemiring R] (hR : (p : R) = 0)
    (T : Type*) [Semiring T] [Algebra R T] : (p : T) = 0 := by
  rw [← map_natCast (algebraMap R T), hR, map_zero]

end CharP
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV"

section Coeff

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]

theorem sum_apply {κ : Type*} (s : Finset κ) (φ : κ → CartierDual R A) (a : A) :
    (∑ i ∈ s, φ i) a = ∑ i ∈ s, φ i a := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]; rfl

theorem smul_apply' (r : R) (φ : CartierDual R A) (a : A) : (r • φ) a = r * φ a := rfl

theorem mul_apply_repr (φ ψ : CartierDual R A) {b : A} {ι : Type*} (𝓡 : Coalgebra.Repr R b ι) :
    (φ * ψ) b = ∑ m ∈ 𝓡.index, φ (𝓡.left m) * ψ (𝓡.right m) := by
  change CartierDual.toDual R A (φ * ψ) b = _
  rw [CartierDual.mul_eq_convMul, Coalgebra.Repr.convMul_apply 𝓡]
  rfl

variable [Coalgebra.IsCocomm R A]
variable {ι : Type w} [Fintype ι] (e : Module.Basis ι R A)

def dualElt (i : ι) : CartierDual R A := CartierDual.ofDual R A (e.coord i)

@[scoped simp] theorem dualElt_apply (i : ι) (a : A) : dualElt e i a = e.repr a i := rfl

theorem sum_dualElt_smul (a : A) : ∑ i, dualElt e i a • e i = a := e.sum_repr a

theorem sum_apply_mul_dualElt (φ : CartierDual R A) (a : A) : ∑ i, φ (e i) * dualElt e i a = φ a := by
  conv_rhs => rw [← sum_dualElt_smul e a, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem eq_sum_smul_dualElt (φ : CartierDual R A) : φ = ∑ i, φ (e i) • dualElt e i := by
  apply CartierDual.ext
  intro a
  rw [sum_apply, ← sum_apply_mul_dualElt e φ a]
  rfl

def E {n : ℕ} (I : Fin n → ι) : CartierDual R A := ∏ j, dualElt e (I j)

def P {n : ℕ} (I : Fin n → ι) : A := ∏ j, e (I j)

theorem E_cons {n : ℕ} (i : ι) (I : Fin n → ι) :
    E e (Fin.cons i I : Fin (n + 1) → ι) = dualElt e i * E e I := by
  unfold E
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem P_cons {n : ℕ} (i : ι) (I : Fin n → ι) :
    P e (Fin.cons i I : Fin (n + 1) → ι) = e i * P e I := by
  unfold P
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem E_comp_perm {n : ℕ} (I : Fin n → ι) (σ : Equiv.Perm (Fin n)) : E e (I ∘ σ) = E e I := by
  unfold E
  exact Equiv.prod_comp σ (fun j => dualElt e (I j))

theorem P_comp_perm {n : ℕ} (I : Fin n → ι) (σ : Equiv.Perm (Fin n)) : P e (I ∘ σ) = P e I := by
  unfold P
  exact Equiv.prod_comp σ (fun j => e (I j))

theorem E_const (n : ℕ) (i : ι) : E e (fun _ : Fin n => i) = dualElt e i ^ n := by
  unfold E
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem P_const (n : ℕ) (i : ι) : P e (fun _ : Fin n => i) = e i ^ n := by
  unfold P
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem sum_fin_succ {n : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin (n + 1) → ι) → M) :
    ∑ I : Fin (n + 1) → ι, F I = ∑ i : ι, ∑ I : Fin n → ι, F (Fin.cons i I) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => ι), Fintype.sum_prod_type]
  rfl

theorem nsmulAlgHom_eq_sum (n : ℕ) (b : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R A n b = ∑ I : Fin n → ι, E e I b • P e I := by
  induction n generalizing b with
  | zero =>
    rw [PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply, Fintype.sum_unique]
    unfold E P
    rw [Fin.prod_univ_zero, Fin.prod_univ_zero, CartierDual.one_apply, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    let 𝓡 := Coalgebra.Repr.arbitrary R b

    have hstep : PDivisibleGroup.Hopf.nsmulAlgHom R A (n + 1) b =
        ∑ m ∈ 𝓡.index, 𝓡.left m * PDivisibleGroup.Hopf.nsmulAlgHom R A n (𝓡.right m) := by
      have h := PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom R A (n + 1)
      rw [pow_succ'] at h
      have h' := congrArg (fun f : A →ₗ[R] A => f b) h
      simp only [AlgHom.toLinearMap_apply] at h'
      rw [h', Coalgebra.Repr.convMul_apply 𝓡]
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      have h2 := congrArg (fun f : A →ₗ[R] A => f (𝓡.right m))
        (PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom R A n)
      simp only [AlgHom.toLinearMap_apply] at h2
      exact h2.symm
    rw [hstep, sum_fin_succ]

    have lhs : ∀ m ∈ 𝓡.index, 𝓡.left m * PDivisibleGroup.Hopf.nsmulAlgHom R A n (𝓡.right m) =
        ∑ i, ∑ I : Fin n → ι, (dualElt e i (𝓡.left m) * E e I (𝓡.right m)) • (e i * P e I) := by
      intro m _
      rw [ih (𝓡.right m)]
      conv_lhs => rw [← sum_dualElt_smul e (𝓡.left m)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [smul_mul_smul_comm]
    rw [Finset.sum_congr rfl lhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [E_cons, P_cons, mul_apply_repr _ _ 𝓡, Finset.sum_smul]

variable (p : ℕ) [hp : Fact p.Prime]

def Q {n : ℕ} (I J : Fin n → ι) : R := ∏ j, dualElt e (I j) (e (J j) ^ p)

theorem Q_cons {n : ℕ} (i₀ i : ι) (I J : Fin n → ι) :
    Q e p (Fin.cons i₀ I : Fin (n + 1) → ι) (Fin.cons i J) = dualElt e i₀ (e i ^ p) * Q e p I J := by
  unfold Q
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

def reprPow (hR : (p : R) = 0) {b : A} {ι : Type*} (𝓡 : Coalgebra.Repr R b ι) : Coalgebra.Repr R (b ^ p) ι where
  index := 𝓡.index
  left m := 𝓡.left m ^ p
  right m := 𝓡.right m ^ p
  eq := by
    rw [Bialgebra.comul_pow, ← 𝓡.eq,
      sum_pow_char' p (cast_eq_zero_of_algebraMap p hR (A ⊗[R] A))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.tmul_pow]

theorem E_apply_pow (hR : (p : R) = 0) (n : ℕ) (I : Fin n → ι) (b : A) :
    E e I (b ^ p) = ∑ J : Fin n → ι, E e J b ^ p * Q e p I J := by
  have hA : (p : A) = 0 := cast_eq_zero_of_algebraMap p hR A
  induction n generalizing b with
  | zero =>
    rw [Fintype.sum_unique]
    unfold E Q
    rw [Fin.prod_univ_zero, Fin.prod_univ_zero, Fin.prod_univ_zero, CartierDual.one_apply,
      CartierDual.one_apply, mul_one, ← Bialgebra.counitAlgHom_apply, map_pow]
    rfl
  | succ n ih =>
    let 𝓡 := Coalgebra.Repr.arbitrary R b

    obtain ⟨⟨i₀, I₁⟩, rfl⟩ := (Fin.consEquiv fun _ : Fin (n + 1) => ι).surjective I
    change E e (Fin.cons i₀ I₁) (b ^ p) = ∑ J : Fin (n + 1) → ι, E e J b ^ p * Q e p (Fin.cons i₀ I₁) J
    rw [E_cons, mul_apply_repr _ _ (reprPow p hR 𝓡), sum_fin_succ]
    change ∑ m ∈ 𝓡.index, dualElt e i₀ (𝓡.left m ^ p) * E e I₁ (𝓡.right m ^ p) = _

    have hleft : ∀ m ∈ 𝓡.index, dualElt e i₀ (𝓡.left m ^ p) =
        ∑ i, dualElt e i (𝓡.left m) ^ p * dualElt e i₀ (e i ^ p) := by
      intro m _
      conv_lhs => rw [← sum_dualElt_smul e (𝓡.left m), sum_pow_char' p hA, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_pow, map_smul, smul_eq_mul]
    have lhs : ∀ m ∈ 𝓡.index, dualElt e i₀ (𝓡.left m ^ p) * E e I₁ (𝓡.right m ^ p) =
        ∑ i, ∑ J : Fin n → ι, dualElt e i (𝓡.left m) ^ p * dualElt e i₀ (e i ^ p) *
          (E e J (𝓡.right m) ^ p * Q e p I₁ J) := by
      intro m hm
      rw [hleft m hm, ih I₁ (𝓡.right m), Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl lhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [E_cons, Q_cons, mul_apply_repr _ _ 𝓡, sum_pow_char' p hR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]
    ring

end Coeff
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV"

end PDivFV
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV"

namespace PDivFV

section Main

universe u v w

open Coalgebra

variable {R : Type u} [CommRing R] (p : ℕ) [hp : Fact p.Prime]
variable {A : Type v} [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
variable {ι : Type w} [Fintype ι] (e : Module.Basis ι R A)

noncomputable def finZ : Fin p ≃ ZMod p := (ZMod.finEquiv p).toEquiv

noncomputable def ρ : Tup ι p ≃ (Fin p → ι) := Equiv.arrowCongr (finZ p).symm (Equiv.refl ι)

theorem ρ_apply (T : Tup ι p) (j : Fin p) : ρ p T j = T (finZ p j) := rfl

noncomputable def rot (r : Multiplicative (ZMod p)) : Equiv.Perm (Fin p) :=
  ((finZ p).trans (Equiv.addRight (Multiplicative.toAdd r))).trans (finZ p).symm

theorem ρ_smul (r : Multiplicative (ZMod p)) (T : Tup ι p) : ρ p (r • T) = ρ p T ∘ rot p r := by
  funext j
  change T (finZ p j + Multiplicative.toAdd r) = T (finZ p ((finZ p).symm (finZ p j + Multiplicative.toAdd r)))
  rw [Equiv.apply_symm_apply]

theorem ρ_const (i : ι) : ρ p (Tup.const i : Tup ι p) = fun _ => i := rfl

theorem sum_eq_sum_const_fin {M : Type*} [AddCommMonoid M] (hM : ∀ m : M, p • m = 0)
    (g : (Fin p → ι) → M) (hg : ∀ (σ : Equiv.Perm (Fin p)) (I : Fin p → ι), g (I ∘ σ) = g I) :
    ∑ I : Fin p → ι, g I = ∑ i : ι, g (fun _ => i) := by
  rw [← Equiv.sum_comp (ρ p)]
  rw [Tup.sum_eq_sum_const hM (fun T => g (ρ p T)) (fun r T => by
    change g (ρ p (r • T)) = g (ρ p T)
    rw [ρ_smul, hg])]
  rfl

theorem nsmulAlgHom_prime_eq (hR : (p : R) = 0) (a : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R A p a = ∑ i, (dualElt e i ^ p) a • e i ^ p := by
  have hA : (p : A) = 0 := cast_eq_zero_of_algebraMap p hR A
  rw [nsmulAlgHom_eq_sum e p a]
  rw [sum_eq_sum_const_fin p (M := A) (fun m => by rw [nsmul_eq_mul, hA, zero_mul])
    (fun I => E e I a • P e I) (fun σ I => by
      change E e (I ∘ σ) a • P e (I ∘ σ) = E e I a • P e I
      rw [E_comp_perm, P_comp_perm])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [E_const, P_const]

theorem pow_apply_pow_eq (e : Module.Basis ι R A) (hR : (p : R) = 0) (φ : CartierDual R A) (a : A) :
    (φ ^ p) (a ^ p) = φ (PDivisibleGroup.Hopf.nsmulAlgHom R A p a) ^ p := by
  classical

  have hrhs : φ (PDivisibleGroup.Hopf.nsmulAlgHom R A p a) =
      ∑ i, E e (fun _ : Fin p => i) a * φ (e i ^ p) := by
    rw [nsmulAlgHom_eq_sum e p a, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [sum_eq_sum_const_fin p (M := R) (fun m => by rw [nsmul_eq_mul, hR, zero_mul])
      (fun I => E e I a * φ (P e I)) (fun σ I => by
        change E e (I ∘ σ) a * φ (P e (I ∘ σ)) = E e I a * φ (P e I)
        rw [E_comp_perm, P_comp_perm])]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [P_const]

  have hpow : φ ^ p = ∑ J : Fin p → ι, (∏ j, φ (e (J j))) • E e J := by
    have h1 : φ ^ p = ∏ _j : Fin p, ∑ i, φ (e i) • dualElt e i := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← eq_sum_smul_dualElt e φ]
    rw [h1]
    refine (Fintype.prod_sum fun (_ : Fin p) (i : ι) => φ (e i) • dualElt e i).trans ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    unfold E
    simp_rw [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  have hlhs : (φ ^ p) (a ^ p) = ∑ K : Fin p → ι, E e K a ^ p * ∏ j, φ (e (K j) ^ p) := by
    rw [hpow, sum_apply]
    simp_rw [smul_apply', E_apply_pow e p hR, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    simp_rw [← mul_assoc, mul_comm _ (E e K a ^ p), mul_assoc, ← Finset.mul_sum]
    congr 1
    unfold Q
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum fun j i => φ (e i) * dualElt e i (e (K j) ^ p)]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact sum_apply_mul_dualElt e φ _
  rw [hlhs, hrhs, sum_pow_char' p hR]
  rw [sum_eq_sum_const_fin p (M := R) (fun m => by rw [nsmul_eq_mul, hR, zero_mul])
    (fun K => E e K a ^ p * ∏ j, φ (e (K j) ^ p)) (fun σ K => by
      change E e (K ∘ σ) a ^ p * ∏ j, φ (e (K (σ j)) ^ p) = E e K a ^ p * ∏ j, φ (e (K j) ^ p)
      rw [E_comp_perm, Equiv.prod_comp σ (fun j => φ (e (K j) ^ p))])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]

end Main
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV"

end PDivFV
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV"

end
p2m_reactivate "P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV.Tup P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.PDivFV"

universe u v in
theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A] (φ : CartierDual R A) (a : A) :
    (φ ^ p) (a ^ p) = φ (PDivisibleGroup.Hopf.nsmulAlgHom R A p a) ^ p :=
  PDivFV.pow_apply_pow_eq p (Module.Free.chooseBasis R A) (CharP.cast_eq_zero R p) φ a

end S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow
end P2MW
export P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow (solution)
