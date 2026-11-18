-- Prove2me | solution 1 for BddExp3SUM.section_2_embedding_exact
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T17:29:11.100221+00:00
-- url     : https://prove2.me/submissions/42552133-bd85-4bc4-8b82-a19b1c1ead83

import Definitions.Def_BddExp3SUM_Embedding


set_option autoImplicit false
namespace BddExp3SUM

namespace EmbeddingProof

def intScale (M m : ℕ) : ℤ →+ ZMod M where
  toFun z := ((M/m : ℕ) : ZMod M)*(z : ZMod M)
  map_zero' := by simp
  map_add' a b := by simp [mul_add]

lemma intScale_period {M m : ℕ} (hm : m∣M) : intScale M m (m:ℤ)=0 := by
  simp only [intScale,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Int.cast_natCast]
  rw [←Nat.cast_mul,Nat.div_mul_cancel hm,ZMod.natCast_self]

def scaledHom {M m : ℕ} (hm : m∣M) : ZMod m →+ ZMod M :=
  ZMod.lift m ⟨intScale M m,intScale_period hm⟩

lemma scaledHom_nat {M m : ℕ} (hm : m∣M) (a : ℕ) :
    scaledHom hm (a:ZMod m)=((M/m*a:ℕ):ZMod M) := by
  have h := ZMod.lift_coe m (⟨intScale M m,intScale_period hm⟩) (a:ℤ)
  simpa only [scaledHom,intScale,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Int.cast_natCast,Nat.cast_mul] using h

lemma scaledHom_val {M m : ℕ} (hM : 0 < M) (hm : m∣M) (a : ZMod m) :
    scaledHom hm a=((M/m*a.val:ℕ):ZMod M) := by
  letI : NeZero m := ⟨ne_of_gt (Nat.pos_of_dvd_of_pos hm hM)⟩
  simpa only [ZMod.natCast_zmod_val] using scaledHom_nat hm a.val

theorem scaledHom_injective {M m : ℕ} (hM : 0 < M) (hm : m∣M) :
    Function.Injective (scaledHom hm) := by
  letI : NeZero M := ⟨hM.ne'⟩
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hM
  letI : NeZero m := ⟨hm0.ne'⟩
  have hs : 0 < M/m := Nat.div_pos (Nat.le_of_dvd hM hm) hm0
  have he : M/m*m=M := Nat.div_mul_cancel hm
  intro a b hab
  rw [scaledHom_val hM hm,scaledHom_val hM hm] at hab
  have ha : M/m*a.val<M := by nlinarith [a.val_lt]
  have hb : M/m*b.val<M := by nlinarith [b.val_lt]
  have hv := congrArg ZMod.val hab
  rw [ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt hb] at hv
  apply ZMod.val_injective m
  exact Nat.eq_of_mul_eq_mul_left hs hv

theorem scale_zero_iff {M m a : ℕ} (hM : 0 < M) (hm : m∣M) :
    ((M/m*a:ℕ):ZMod M)=0 ↔ a%m=0 := by
  rw [ZMod.natCast_eq_zero_iff]
  have hs : 0 < M/m := Nat.div_pos (Nat.le_of_dvd hM hm) (Nat.pos_of_dvd_of_pos hm hM)
  conv_lhs => lhs; rw [← Nat.div_mul_cancel hm]
  rw [Nat.mul_dvd_mul_iff_left hs,Nat.dvd_iff_mod_eq_zero]

theorem section_2_embedding (M : ℕ) (hM : 2≤M) :
    (∀ m : ℕ, m∣M → ∃ f : ZMod m →+ ZMod M, Function.Injective f ∧
      ∀ y : ZMod m,f y=((M/m*y.val:ℕ):ZMod M)) ∧
    ∀ x : Instance M,
      (∀ a a' : Fin x.r → ℕ,(∀ j,a j < x.m j) → (∀ j,a' j < x.m j) →
        x.embed a=x.embed a' → a=a') ∧
      ∀ a₁ a₂ a₃ : Fin x.r → ℕ,
        x.ZeroSum a₁ a₂ a₃ ↔ x.embed a₁+x.embed a₂+x.embed a₃=0 := by
  have hM0 : 0 < M := by omega
  constructor
  · intro m hm
    exact ⟨scaledHom hm,scaledHom_injective hM0 hm,scaledHom_val hM0 hm⟩
  · intro x
    constructor
    · intro a b ha hb hab
      funext j
      have hj := congrFun hab j
      change ((M/x.m j*a j:ℕ):ZMod M)=((M/x.m j*b j:ℕ):ZMod M) at hj
      rw [←scaledHom_nat (x.m_dvd j),←scaledHom_nat (x.m_dvd j)] at hj
      have he := scaledHom_injective hM0 (x.m_dvd j) hj
      have hv := congrArg ZMod.val he
      simpa only [ZMod.val_natCast_of_lt (ha j),ZMod.val_natCast_of_lt (hb j)] using hv
    · intro a b c
      change (∀ j,(a j+b j+c j)%x.m j=0) ↔ _
      constructor
      · intro hz
        funext j
        have hj := (scale_zero_iff hM0 (x.m_dvd j)).mpr (hz j)
        simpa only [Instance.embed,Pi.add_apply,Pi.zero_apply,Nat.mul_add,Nat.cast_add] using hj
      · intro hz j
        apply (scale_zero_iff hM0 (x.m_dvd j)).mp
        have hj := congrFun hz j
        simpa only [Instance.embed,Pi.add_apply,Pi.zero_apply,Nat.mul_add,Nat.cast_add] using hj

end EmbeddingProof

end BddExp3SUM

open BddExp3SUM

theorem solution (M : ℕ) (hM : 2 ≤ M) :
    (∀ m : ℕ, m ∣ M → ∃ f : ZMod m →+ ZMod M, Function.Injective f ∧
      ∀ y : ZMod m, f y = ((M / m * y.val : ℕ) : ZMod M)) ∧
    ∀ x : Instance M,
      (∀ a a' : Fin x.r → ℕ, (∀ j, a j < x.m j) → (∀ j, a' j < x.m j) →
        x.embed a = x.embed a' → a = a') ∧
      ∀ a₁ a₂ a₃ : Fin x.r → ℕ,
        x.ZeroSum a₁ a₂ a₃ ↔ x.embed a₁ + x.embed a₂ + x.embed a₃ = 0  := BddExp3SUM.EmbeddingProof.section_2_embedding M hM
