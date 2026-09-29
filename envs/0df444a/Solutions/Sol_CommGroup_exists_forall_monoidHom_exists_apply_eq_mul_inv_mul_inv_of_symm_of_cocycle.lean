-- Prove2me | solution 1 for CommGroup.exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e444fa8a-c1f1-574e-9362-9259679ee256

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle

set_option autoImplicit false

universe u v

namespace SymmCocycSplit

variable {K : Type u} [AddCommGroup K] {A : Type v} [CommGroup A]

structure Cocyc (K : Type u) [AddCommGroup K] (A : Type v) [CommGroup A] where
  c : K → K → A
  symm : ∀ k k', c k k' = c k' k
  coc : ∀ k k' k'', c k k' * c (k + k') k'' = c k' k'' * c k (k' + k'')

namespace Cocyc

variable (C : Cocyc K A)

theorem c_zero_right (k : K) : C.c k 0 = C.c 0 0 := by
  have h := C.coc k 0 0
  rw [add_zero, zero_add] at h

  exact mul_right_cancel h

theorem c_zero_left (k : K) : C.c 0 k = C.c 0 0 := by
  rw [C.symm]; exact C.c_zero_right k

def map {A' : Type v} [CommGroup A'] (φ : A →* A') : Cocyc K A' where
  c := fun k k' => φ (C.c k k')
  symm := fun k k' => by rw [C.symm]
  coc := fun k k' k'' => by rw [← map_mul, ← map_mul, C.coc]

@[scoped simp] theorem map_c {A' : Type v} [CommGroup A'] (φ : A →* A') (k k' : K) : (C.map φ).c k k' = φ (C.c k k') := rfl

end Cocyc
p2m_reactivate "P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle.SymmCocycSplit.Cocyc"

def Tw (C : Cocyc K A) : Type (max u v) := A × K

namespace Tw

variable {C : Cocyc K A}

def mk (x : A) (k : K) : Tw C := (x, k)
def fstA (z : Tw C) : A := z.1
def sndK (z : Tw C) : K := z.2

@[scoped simp] theorem fstA_mk (x : A) (k : K) : fstA (mk (C := C) x k) = x := rfl
@[scoped simp] theorem sndK_mk (x : A) (k : K) : sndK (mk (C := C) x k) = k := rfl
theorem mk_fstA_sndK (z : Tw C) : mk z.fstA z.sndK = z := rfl

@[scoped ext] theorem ext {z w : Tw C} (h1 : z.fstA = w.fstA) (h2 : z.sndK = w.sndK) : z = w := Prod.ext h1 h2

scoped instance : CommGroup (Tw C) where
  mul z w := mk (z.fstA * w.fstA * C.c z.sndK w.sndK) (z.sndK + w.sndK)
  one := mk (C.c 0 0)⁻¹ 0
  inv z := mk (z.fstA⁻¹ * (C.c z.sndK (-z.sndK))⁻¹ * (C.c 0 0)⁻¹) (-z.sndK)
  mul_assoc z w t := by
    apply ext
    · show z.fstA * w.fstA * C.c z.sndK w.sndK * t.fstA * C.c (z.sndK + w.sndK) t.sndK =
        z.fstA * (w.fstA * t.fstA * C.c w.sndK t.sndK) * C.c z.sndK (w.sndK + t.sndK)
      have h := C.coc z.sndK w.sndK t.sndK
      calc z.fstA * w.fstA * C.c z.sndK w.sndK * t.fstA * C.c (z.sndK + w.sndK) t.sndK
          = z.fstA * w.fstA * t.fstA * (C.c z.sndK w.sndK * C.c (z.sndK + w.sndK) t.sndK) := by simp only [mul_assoc, mul_comm, mul_left_comm]
        _ = z.fstA * w.fstA * t.fstA * (C.c w.sndK t.sndK * C.c z.sndK (w.sndK + t.sndK)) := by rw [h]
        _ = _ := by simp only [mul_assoc, mul_comm, mul_left_comm]
    · show z.sndK + w.sndK + t.sndK = z.sndK + (w.sndK + t.sndK)
      exact add_assoc _ _ _
  one_mul z := by
    apply ext
    · show (C.c 0 0)⁻¹ * z.fstA * C.c 0 z.sndK = z.fstA
      rw [C.c_zero_left z.sndK, mul_right_comm, inv_mul_cancel, one_mul]
    · show 0 + z.sndK = z.sndK
      exact zero_add _
  mul_one z := by
    apply ext
    · show z.fstA * (C.c 0 0)⁻¹ * C.c z.sndK 0 = z.fstA
      rw [C.c_zero_right z.sndK, mul_assoc, inv_mul_cancel, mul_one]
    · show z.sndK + 0 = z.sndK
      exact add_zero _
  inv_mul_cancel z := by
    apply ext
    · show z.fstA⁻¹ * (C.c z.sndK (-z.sndK))⁻¹ * (C.c 0 0)⁻¹ * z.fstA * C.c (-z.sndK) z.sndK = (C.c 0 0)⁻¹
      rw [C.symm (-z.sndK) z.sndK]
      have h : z.fstA⁻¹ * (C.c z.sndK (-z.sndK))⁻¹ * (C.c 0 0)⁻¹ * z.fstA * C.c z.sndK (-z.sndK) =
          (z.fstA⁻¹ * z.fstA) * ((C.c z.sndK (-z.sndK))⁻¹ * C.c z.sndK (-z.sndK)) * (C.c 0 0)⁻¹ := by ac_rfl
      rw [h, inv_mul_cancel, inv_mul_cancel, one_mul, one_mul]
    · show -z.sndK + z.sndK = 0
      exact neg_add_cancel _
  mul_comm z w := by
    apply ext
    · show z.fstA * w.fstA * C.c z.sndK w.sndK = w.fstA * z.fstA * C.c w.sndK z.sndK
      rw [C.symm z.sndK w.sndK, mul_comm z.fstA w.fstA]
    · show z.sndK + w.sndK = w.sndK + z.sndK
      exact add_comm _ _

theorem mul_def (z w : Tw C) : z * w = mk (z.fstA * w.fstA * C.c z.sndK w.sndK) (z.sndK + w.sndK) := rfl
theorem one_def : (1 : Tw C) = mk (C.c 0 0)⁻¹ 0 := rfl
@[scoped simp] theorem fstA_mul (z w : Tw C) : (z * w).fstA = z.fstA * w.fstA * C.c z.sndK w.sndK := rfl
@[scoped simp] theorem sndK_mul (z w : Tw C) : (z * w).sndK = z.sndK + w.sndK := rfl
@[scoped simp] theorem fstA_one : (1 : Tw C).fstA = (C.c 0 0)⁻¹ := rfl
@[scoped simp] theorem sndK_one : (1 : Tw C).sndK = 0 := rfl
@[scoped simp] theorem sndK_inv (z : Tw C) : z⁻¹.sndK = -z.sndK := rfl
@[scoped simp] theorem fstA_inv (z : Tw C) : z⁻¹.fstA = z.fstA⁻¹ * (C.c z.sndK (-z.sndK))⁻¹ * (C.c 0 0)⁻¹ := rfl

def π : Tw C →* Multiplicative K where
  toFun z := Multiplicative.ofAdd z.sndK
  map_one' := rfl
  map_mul' _ _ := rfl

@[scoped simp] theorem π_apply (z : Tw C) : π z = Multiplicative.ofAdd z.sndK := rfl

theorem sndK_pow (z : Tw C) (n : ℕ) : (z ^ n).sndK = n • z.sndK := by
  have := map_pow (π (C := C)) z n
  simp only [π_apply] at this
  rw [← ofAdd_nsmul] at this
  exact Multiplicative.ofAdd.injective this

theorem sndK_prod {ι : Type} (s : Finset ι) (f : ι → Tw C) : (∏ i ∈ s, f i).sndK = ∑ i ∈ s, (f i).sndK := by
  have := map_prod (π (C := C)) f s
  simp only [π_apply] at this
  rw [← ofAdd_sum] at this
  exact Multiplicative.ofAdd.injective this

def ι : A →* Tw C where
  toFun x := mk (x * (C.c 0 0)⁻¹) 0
  map_one' := by apply ext <;> simp [one_def]
  map_mul' x y := by
    apply ext
    · show x * y * (C.c 0 0)⁻¹ = x * (C.c 0 0)⁻¹ * (y * (C.c 0 0)⁻¹) * C.c 0 0
      have h : x * (C.c 0 0)⁻¹ * (y * (C.c 0 0)⁻¹) * C.c 0 0 = x * y * (C.c 0 0)⁻¹ * ((C.c 0 0)⁻¹ * C.c 0 0) := by ac_rfl
      rw [h, inv_mul_cancel, mul_one]
    · show (0 : K) = 0 + 0
      rw [add_zero]

@[scoped simp] theorem fstA_ι (x : A) : (ι (C := C) x).fstA = x * (C.c 0 0)⁻¹ := rfl
@[scoped simp] theorem sndK_ι (x : A) : (ι (C := C) x).sndK = 0 := rfl

theorem eq_ι_of_sndK_eq_zero (z : Tw C) (hz : z.sndK = 0) : z = ι (z.fstA * C.c 0 0) := by
  apply ext
  · simp
  · simpa using hz

def mapA {A' : Type v} [CommGroup A'] (φ : A →* A') : Tw C →* Tw (C.map φ) where
  toFun z := mk (φ z.fstA) z.sndK
  map_one' := by
    apply ext
    · show φ (C.c 0 0)⁻¹ = ((C.map φ).c 0 0)⁻¹; rw [map_inv]; rfl
    · rfl
  map_mul' z w := by
    apply ext
    · show φ (z.fstA * w.fstA * C.c z.sndK w.sndK) = φ z.fstA * φ w.fstA * (C.map φ).c z.sndK w.sndK
      rw [map_mul, map_mul]; rfl
    · rfl

@[scoped simp] theorem fstA_mapA {A' : Type v} [CommGroup A'] (φ : A →* A') (z : Tw C) : (mapA φ z).fstA = φ z.fstA := rfl
@[scoped simp] theorem sndK_mapA {A' : Type v} [CommGroup A'] (φ : A →* A') (z : Tw C) : (mapA φ z).sndK = z.sndK := rfl

end Tw
p2m_reactivate "P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle.SymmCocycSplit.Cocyc P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle.SymmCocycSplit.Tw"

end SymmCocycSplit
p2m_reactivate "P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle.SymmCocycSplit.Cocyc P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle.SymmCocycSplit.Tw P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle.SymmCocycSplit"

open SymmCocycSplit

theorem solution
    {K : Type u} [AddCommGroup K] [Finite K] {A : Type v} [CommGroup A] (c : K → K → A)
    (hsymm : ∀ k k', c k k' = c k' k) (hcoc : ∀ k k' k'', c k k' * c (k + k') k'' = c k' k'' * c k (k' + k'')) :
    ∃ (m : ℕ) (a : Fin m → A) (n : Fin m → ℕ), (∀ i, 0 < n i ∧ n i ∣ Nat.card K) ∧
      ∀ (A' : Type v) [CommGroup A'] (φ : A →* A'), (∀ i, ∃ α : A', α ^ (n i) = φ (a i)) →
        ∃ b : K → A', ∀ k k', φ (c k k') = b (k + k') * (b k)⁻¹ * (b k')⁻¹ := by
  classical

  obtain ⟨ι, _hι, N, hN, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' K
  haveI : ∀ i, NeZero (N i) := fun i => ⟨by have := hN i; omega⟩
  let C : Cocyc K A := ⟨c, hsymm, hcoc⟩

  let gen : ι → K := fun i => e.symm (DirectSum.of (fun i => ZMod (N i)) i 1)
  have hgen_ord : ∀ i, N i • gen i = 0 := by
    intro i
    show N i • e.symm (DirectSum.of (fun i => ZMod (N i)) i 1) = 0
    rw [← map_nsmul, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero, map_zero]
  have hdecomp : ∀ k : K, k = ∑ i, ((e k) i).val • gen i := by
    intro k
    apply e.injective
    rw [map_sum]
    conv_lhs => rw [← DirectSum.sum_univ_of (e k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    show DirectSum.of (fun i => ZMod (N i)) i ((e k) i) = e (((e k) i).val • e.symm (DirectSum.of (fun i => ZMod (N i)) i 1))
    rw [map_nsmul, AddEquiv.apply_symm_apply, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

  let m := Fintype.card ι
  let σ : Fin m ≃ ι := (Fintype.equivFin ι).symm
  let lift : ι → Tw C := fun i => Tw.mk 1 (gen i)
  let a : Fin m → A := fun j => C.c 0 0 * ((lift (σ j)) ^ (N (σ j))).fstA
  refine ⟨m, a, fun j => N (σ j), fun j => ⟨Nat.pos_of_ne_zero (NeZero.ne _), ?_⟩, ?_⟩
  ·
    have hord : addOrderOf (gen (σ j)) = N (σ j) := by
      have : addOrderOf (DirectSum.of (fun i => ZMod (N i)) (σ j) (1 : ZMod (N (σ j)))) = N (σ j) := by
        rw [addOrderOf_injective (DirectSum.of (fun i => ZMod (N i)) (σ j)) (DirectSum.of_injective _) 1]
        exact ZMod.addOrderOf_one _
      rw [← this]
      exact (AddEquiv.addOrderOf_eq e.symm _)
    show N (σ j) ∣ Nat.card K
    rw [← hord]
    exact addOrderOf_dvd_natCard _
  · intro A' _ φ hroots
    let C' : Cocyc K A' := C.map φ

    have key : ∀ i : ι, ∃ z : Tw C', z.sndK = gen i ∧ z ^ (N i) = 1 := by
      intro i
      obtain ⟨α, hα⟩ := hroots (σ.symm i)
      simp only [Equiv.apply_symm_apply] at hα

      refine ⟨Tw.mapA φ (lift i) * (Tw.ι α)⁻¹, ?_, ?_⟩
      · rw [Tw.sndK_mul, Tw.sndK_inv, Tw.sndK_ι, neg_zero, add_zero, Tw.sndK_mapA]
        rfl
      · rw [mul_pow, inv_pow, ← map_pow, ← map_pow]
        have h1 : (Tw.mapA φ ((lift i) ^ N i) : Tw C') = Tw.ι (φ (a (σ.symm i))) := by
          have hz : (Tw.mapA φ ((lift i) ^ N i) : Tw C').sndK = 0 := by
            rw [Tw.sndK_mapA, Tw.sndK_pow]
            show N i • gen i = 0
            exact hgen_ord i
          rw [Tw.eq_ι_of_sndK_eq_zero _ hz]
          congr 1
          simp only [Tw.fstA_mapA, a, Equiv.apply_symm_apply, map_mul]
          rw [mul_comm]; rfl
        rw [h1, ← hα, map_pow, mul_inv_cancel]
    choose z hz1 hz2 using key

    let s : K → Tw C' := fun k => ∏ i, (z i) ^ ((e k) i).val
    have hs_snd : ∀ k, (s k).sndK = k := by
      intro k
      show (∏ i, (z i) ^ ((e k) i).val).sndK = k
      rw [Tw.sndK_prod]
      conv_rhs => rw [hdecomp k]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Tw.sndK_pow, hz1]
    have hpowmod : ∀ (i : ι) (n : ℕ), (z i) ^ n = (z i) ^ (n % N i) := by
      intro i n
      conv_lhs => rw [← Nat.mod_add_div n (N i), pow_add, pow_mul, hz2 i, one_pow, mul_one]
    have hs_mul : ∀ k k', s (k + k') = s k * s k' := by
      intro k k'
      show (∏ i, (z i) ^ ((e (k + k')) i).val) = (∏ i, (z i) ^ ((e k) i).val) * ∏ i, (z i) ^ ((e k') i).val
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, map_add, DirectSum.add_apply, ZMod.val_add, ← hpowmod, hpowmod i (((e k) i).val + ((e k') i).val)]

    refine ⟨fun k => (s k).fstA, fun k k' => ?_⟩
    have h := congrArg Tw.fstA (hs_mul k k')
    rw [Tw.fstA_mul, hs_snd, hs_snd] at h

    show φ (c k k') = (s (k + k')).fstA * ((s k).fstA)⁻¹ * ((s k').fstA)⁻¹
    rw [h]
    show φ (c k k') = (s k).fstA * (s k').fstA * φ (c k k') * ((s k).fstA)⁻¹ * ((s k').fstA)⁻¹
    have hre : (s k).fstA * (s k').fstA * φ (c k k') * ((s k).fstA)⁻¹ * ((s k').fstA)⁻¹ =
        φ (c k k') * ((s k).fstA * ((s k).fstA)⁻¹) * ((s k').fstA * ((s k').fstA)⁻¹) := by ac_rfl
    rw [hre, mul_inv_cancel, mul_inv_cancel, mul_one, mul_one]

end S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle
end P2MW
export P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle (solution)
