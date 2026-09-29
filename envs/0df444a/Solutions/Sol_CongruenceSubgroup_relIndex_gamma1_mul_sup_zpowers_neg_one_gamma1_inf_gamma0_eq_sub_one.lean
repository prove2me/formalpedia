-- Prove2me | solution 1 for CongruenceSubgroup.relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5e58ed1b-e9c8-5bf5-b914-b15c4f758c8f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one

set_option autoImplicit false

open scoped MatrixGroups

namespace Ws28
namespace S1

open CongruenceSubgroup

theorem gamma1_mul_le (M p : ℕ) : Gamma1 (M * p) ≤ Gamma1 M ⊓ Gamma0 p := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h00
      rwa [map_intCast, map_one] at this
    · have := congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h11
      rwa [map_intCast, map_one] at this
    · have := congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h10
      rwa [map_intCast, map_zero] at this
  · rw [Gamma0_mem]
    have := congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) h10
    rwa [map_intCast, map_zero] at this

theorem T_mem (M p : ℕ) : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 p := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem, ModularGroup.coe_T]
    simp
  · rw [Gamma0_mem, ModularGroup.coe_T]
    simp

theorem neg_one_notMem_gamma1 (M : ℕ) (hM : 3 ≤ M) : (-1 : SL(2, ℤ)) ∉ Gamma1 M := by
  intro h
  rw [Gamma1_mem] at h
  have h00 : ((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M) = -1 := by
    simp [Matrix.SpecialLinearGroup.coe_neg]
  have h2 : ((2 : ℤ) : ZMod M) = 0 := by
    have e : (-1 : ZMod M) = 1 := h00.symm.trans h.1
    have e2 : (2 : ZMod M) = 1 - (-1) := by ring
    rw [Int.cast_ofNat, e2, e, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have h3 : (M : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
  omega

theorem mem_or_neg_mem_of_mem_sup (X : Subgroup SL(2, ℤ)) {γ : SL(2, ℤ)}
    (hγ : γ ∈ X ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) : γ ∈ X ∨ -γ ∈ X := by
  rw [Subgroup.sup_eq_closure] at hγ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inl hx
    ·
      have hx1 : x = 1 ∨ x = -1 := by
        have hx' : x ∈ Subgroup.closure {(-1 : SL(2, ℤ))} := by
          rw [← Subgroup.zpowers_eq_closure]; exact hx
        clear hx
        induction hx' using Subgroup.closure_induction with
        | mem y hy => exact Or.inr hy
        | one => exact Or.inl rfl
        | mul y z _ _ hy hz =>
          rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
          · exact Or.inl (one_mul 1)
          · exact Or.inr (one_mul _)
          · exact Or.inr (mul_one _)
          · left; rw [neg_mul_neg, one_mul]
        | inv y _ hy =>
          rcases hy with rfl | rfl
          · exact Or.inl inv_one
          · right; rw [← neg_inv, inv_one]
      rcases hx1 with rfl | rfl
      · exact Or.inl X.one_mem
      · right; rw [neg_neg]; exact X.one_mem
  | one => exact Or.inl X.one_mem
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (X.mul_mem hx hy)
    · right; rw [← mul_neg]; exact X.mul_mem hx hy
    · right; rw [← neg_mul]; exact X.mul_mem hx hy
    · left; rw [← neg_mul_neg]; exact X.mul_mem hx hy
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (X.inv_mem hx)
    · right; rw [neg_inv]; exact X.inv_mem hx

theorem relIndex_sup_zpowers_neg_one_eq_two (X : Subgroup SL(2, ℤ)) (hX : (-1 : SL(2, ℤ)) ∉ X) :
    X.relIndex (X ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mul_neg_one]
  have hb := mem_or_neg_mem_of_mem_sup X b.2
  have hnot : ¬ ((-(b : SL(2, ℤ))) ∈ X ∧ (b : SL(2, ℤ)) ∈ X) := by
    rintro ⟨h1, h2⟩
    apply hX
    have := X.mul_mem h1 (X.inv_mem h2)
    rwa [neg_mul, mul_inv_cancel] at this
  rcases hb with h | h
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩

noncomputable def dChar (M p : ℕ) : ↥(Gamma1 M ⊓ Gamma0 p) →* (ZMod p)ˣ :=
  ((Gamma0Map p).comp (Subgroup.inclusion inf_le_right)).toHomUnits

theorem val_dChar (M p : ℕ) (γ : ↥(Gamma1 M ⊓ Gamma0 p)) :
    ((dChar M p γ : (ZMod p)ˣ) : ZMod p) = ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p) := rfl

theorem intCast_eq_one_iff (n : ℕ) (z : ℤ) : ((z : ℤ) : ZMod n) = 1 ↔ (n : ℤ) ∣ z - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, sub_eq_zero]

theorem isCoprime_of_not_dvd (M p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) : IsCoprime (M : ℤ) (p : ℤ) :=
  Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpM).symm

theorem dChar_eq_one_iff (M p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (γ : ↥(Gamma1 M ⊓ Gamma0 p)) :
    dChar M p γ = 1 ↔ (γ : SL(2, ℤ)) ∈ Gamma1 (M * p) := by
  have hcop := isCoprime_of_not_dvd M p hpM
  have hMp : ∀ w : ℤ, (M : ℤ) ∣ w → (p : ℤ) ∣ w → ((M * p : ℕ) : ℤ) ∣ w := fun w h1 h2 => by
    rw [Nat.cast_mul]; exact hcop.mul_dvd h1 h2
  obtain ⟨hG1, hG0⟩ := Subgroup.mem_inf.mp γ.2
  rw [Gamma1_mem] at hG1
  rw [Gamma0_mem] at hG0
  obtain ⟨ha, hd, hc⟩ := hG1
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  rw [Units.ext_iff, val_dChar, Units.val_one, Gamma1_mem]
  constructor
  · intro hdp

    have hap : ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod p) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod p)) hdet
      push_cast at this
      rw [hdp, hG0, mul_one, mul_zero, sub_zero] at this
      exact this
    refine ⟨?_, ?_, ?_⟩
    · rw [intCast_eq_one_iff] at ha hap ⊢
      exact hMp _ ha hap
    · rw [intCast_eq_one_iff] at hd hdp ⊢
      exact hMp _ hd hdp
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc hG0 ⊢
      exact hMp _ hc hG0
  · rintro ⟨-, hd', -⟩
    have := congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) hd'
    rwa [map_intCast, map_one] at this

theorem dChar_surjective (M p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) : Function.Surjective (dChar M p) := by
  intro u
  have hcop := isCoprime_of_not_dvd M p hpM
  obtain ⟨x, y, hxy⟩ := hcop

  set t : ℤ := (((u : ZMod p)).val : ℤ) with ht
  set s : ℤ := (((u⁻¹ : (ZMod p)ˣ) : ZMod p).val : ℤ) with hs
  have htu : ((t : ℤ) : ZMod p) = (u : ZMod p) := by
    rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hsu : ((s : ℤ) : ZMod p) = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    rw [hs, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hts : (p : ℤ) ∣ t * s - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul, Int.cast_one, htu, hsu, Units.mul_inv, sub_self]
  obtain ⟨k, hk⟩ := hts

  set d : ℤ := t - y * p * (t - 1) with hd
  have hdM : IsCoprime d (M : ℤ) := ⟨1, -(x * (t - 1)), by rw [hd]; linear_combination (-(t - 1)) * hxy⟩
  have hdp : IsCoprime d (p : ℤ) := ⟨s, -k + s * (y * (t - 1)), by rw [hd]; linear_combination hk⟩
  obtain ⟨a, b, hab⟩ := hdM.mul_right hdp

  have hdet : Matrix.det !![a, -b; (M : ℤ) * p, d] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hab
  have hdmodM : ((d : ℤ) : ZMod M) = 1 := by
    rw [intCast_eq_one_iff]
    exact ⟨(t - 1) * x, by rw [hd]; linear_combination (-(t - 1)) * hxy⟩
  have hdmodp : ((d : ℤ) : ZMod p) = (u : ZMod p) := by
    rw [← htu, hd]; push_cast; rw [ZMod.natCast_self]; ring
  have hamodM : ((a : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod M)) hab
    push_cast at this
    rw [hdmodM, ZMod.natCast_self] at this
    simpa using this
  let γ : SL(2, ℤ) := ⟨!![a, -b; (M : ℤ) * p, d], hdet⟩
  have hγ00 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = a := by
    show (!![a, -b; (M : ℤ) * p, d] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = a
    simp
  have hγ11 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = d := by
    show (!![a, -b; (M : ℤ) * p, d] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = d
    simp
  have hγ10 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (M : ℤ) * p := by
    show (!![a, -b; (M : ℤ) * p, d] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (M : ℤ) * p
    simp
  have hγ1 : γ ∈ Gamma1 M := by
    refine (Gamma1_mem M γ).mpr ⟨?_, ?_, ?_⟩
    · rw [hγ00]; exact hamodM
    · rw [hγ11]; exact hdmodM
    · rw [hγ10]; push_cast; rw [ZMod.natCast_self, zero_mul]
  have hγ0 : γ ∈ Gamma0 p := by
    refine Gamma0_mem.mpr ?_
    rw [hγ10]; push_cast; rw [ZMod.natCast_self, mul_zero]
  refine ⟨⟨γ, Subgroup.mem_inf.mpr ⟨hγ1, hγ0⟩⟩, Units.ext ?_⟩
  rw [val_dChar]
  show ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p) = (u : ZMod p)
  rw [hγ11]
  exact hdmodp

theorem relIndex_gamma1_mul (M p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) :
    (Gamma1 (M * p)).relIndex (Gamma1 M ⊓ Gamma0 p) = p - 1 := by
  have hker : (dChar M p).ker = (Gamma1 (M * p)).subgroupOf (Gamma1 M ⊓ Gamma0 p) := by
    ext γ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, dChar_eq_one_iff M p hpM]
  have hrange : (dChar M p).range = ⊤ := MonoidHom.range_eq_top.mpr (dChar_surjective M p hpM)
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
    ZMod.card_units]

end Ws28.S1

open Ws28.S1 CongruenceSubgroup in
theorem solution
    (M p : ℕ) [NeZero M] (hM : 3 ≤ M) [Fact p.Prime] (hpM : ¬ p ∣ M) :
    CongruenceSubgroup.Gamma1 (M * p) ≤ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ∧
    ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ∧
    (∀ γ ∈ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)),
        γ ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ∨
          -γ ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) ∧
    (CongruenceSubgroup.Gamma1 (M * p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).relIndex
        ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) = p - 1 := by
  have h1 := gamma1_mul_le M p
  have hnegM := neg_one_notMem_gamma1 M hM
  have hnegG : (-1 : SL(2, ℤ)) ∉ Gamma1 M ⊓ Gamma0 p := fun h => hnegM (Subgroup.mem_inf.mp h).1
  have hnegA : (-1 : SL(2, ℤ)) ∉ Gamma1 (M * p) := fun h => hnegG (h1 h)
  refine ⟨h1, T_mem M p, fun γ hγ => mem_or_neg_mem_of_mem_sup _ hγ, ?_⟩
  have e1 := Subgroup.relIndex_mul_relIndex (Gamma1 (M * p)) (Gamma1 (M * p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) le_sup_left (sup_le_sup_right h1 _)
  have e2 := Subgroup.relIndex_mul_relIndex (Gamma1 (M * p)) (Gamma1 M ⊓ Gamma0 p)
    ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) h1 le_sup_left
  rw [relIndex_sup_zpowers_neg_one_eq_two _ hnegA] at e1
  rw [relIndex_sup_zpowers_neg_one_eq_two _ hnegG, relIndex_gamma1_mul M p hpM] at e2
  omega

end S_CongruenceSubgroup_relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one
end P2MW
export P2MW.S_CongruenceSubgroup_relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one (solution)
