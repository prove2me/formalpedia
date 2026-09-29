-- Prove2me | solution 1 for CohCarrier.surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4a0ae545-8061-5176-9625-16abfd7e75be

import Mathlib
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure
import Theorems.Thm_Matrix_SpecialLinearGroup_nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace GammaHDescentSol

open CohCarrier

section Free

variable (L : ℕ) [NeZero L] (H' : Subgroup (ZMod L)ˣ) (r : ℕ) (hrL : r ∣ L) (hr : 4 ≤ r)
  (hH' : ∀ u ∈ H', ZMod.castHom hrL (ZMod r) (u : ZMod L) = 1)

theorem Gamma_le_GammaH : Gamma L ≤ GammaH L H' := by
  intro A hA
  rw [Gamma_mem] at hA
  obtain ⟨_, _, h10, h11⟩ := hA
  rw [mem_GammaH_iff]
  refine ⟨by rw [Gamma0_mem]; exact h10, ?_⟩
  have : gamma0Units L ⟨A, by rw [Gamma0_mem]; exact h10⟩ = 1 := by
    ext
    rw [val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H'

scoped instance GammaH_finiteIndex : (GammaH L H').FiniteIndex :=
  IsCongruenceSubgroup.finiteIndex ⟨L, NeZero.ne L, Gamma_le_GammaH L H'⟩

theorem eq_one_or_eq_neg_one_of_mem_center {z : SL(2, ℤ)} (hz : z ∈ Subgroup.center SL(2, ℤ)) :
    z = 1 ∨ z = -1 := by
  rw [mem_center_iff] at hz
  obtain ⟨t, ht, hz⟩ := hz
  simp only [Fintype.card_fin] at ht
  have htu : t = 1 ∨ t = -1 := Int.isUnit_iff.mp (IsUnit.of_pow_eq_one ht two_ne_zero)
  rcases htu with rfl | rfl
  · left
    apply Subtype.ext
    rw [← hz]
    simp
  · right
    apply Subtype.ext
    rw [← hz, coe_neg]
    simp

include hH' hr in

theorem entries_mod_r (γ : ↥(GammaH L H')) :
    (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod r) = 1 ∧ (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod r) = 1 := by
  obtain ⟨h0, hH⟩ := mem_GammaH_iff.mp γ.2
  have hd : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod r) = 1 := by
    have := hH' _ hH
    rw [val_gamma0Units] at this
    change ZMod.castHom hrL (ZMod r) ((((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod L)) = 1 at this
    rwa [map_intCast] at this
  refine ⟨hd, ?_⟩
  have hda := Gamma0_d_mul_a L ⟨γ, h0⟩
  have := congrArg (ZMod.castHom hrL (ZMod r)) hda
  rw [map_mul, map_one, map_intCast, map_intCast] at this
  change (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod r) * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod r) = 1 at this
  rwa [hd, one_mul] at this

include hH' hr in

theorem trace_ne (γ : ↥(GammaH L H')) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (t : ℤ)
    (ht : t = 0 ∨ t = 1 ∨ t = -1) :
    ε * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ t := by
  obtain ⟨hd, ha⟩ := entries_mod_r L H' r hrL hr hH' γ
  intro htr
  rw [Matrix.trace_fin_two] at htr

  have hsum : ((γ : SL(2, ℤ)) 0 0 : ℤ) + (γ : SL(2, ℤ)) 1 1 = ε * t := by
    rcases hε with rfl | rfl
    · rw [one_mul] at htr ⊢; exact htr
    · rw [neg_one_mul] at htr ⊢; rw [← htr, neg_neg]
  have h2 : ((2 - ε * t : ℤ) : ZMod r) = 0 := by
    rw [← hsum]
    push_cast
    rw [ha, hd]
    ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have hpos : 0 < 2 - ε * t ∧ 2 - ε * t ≤ 3 := by
    rcases hε with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> norm_num
  have hle := Int.le_of_dvd hpos.1 h2
  omega

include hH' hr in
theorem neg_one_notMem : (-1 : SL(2, ℤ)) ∉ GammaH L H' := by
  intro hmem
  obtain ⟨hd, _⟩ := entries_mod_r L H' r hrL hr hH' ⟨-1, hmem⟩
  simp only [coe_neg, coe_one] at hd
  have : ((-1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) = -1 := by simp
  rw [this] at hd
  push_cast at hd

  have h2 : ((2 : ℤ) : ZMod r) = 0 := by
    have := congrArg (fun x : ZMod r => 1 - x) hd
    simp only [sub_neg_eq_add, sub_self] at this
    rw [← this]; push_cast; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have := Int.le_of_dvd (by norm_num) h2
  omega

include hH' hr in

theorem isFreeGroup_GammaH : IsFreeGroup ↥(GammaH L H') := by
  let π : SL(2, ℤ) →* SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ) :=
    QuotientGroup.mk' (Subgroup.center SL(2, ℤ))
  let Γ' : Subgroup SL(2, ℤ) := GammaH L H'
  let Γpm : Subgroup SL(2, ℤ) := (Γ'.map π).comap π
  have hle : Γ' ≤ Γpm := Subgroup.le_comap_map π Γ'
  haveI : Γpm.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hneg : (-1 : SL(2, ℤ)) ∈ Γpm := by
    rw [Subgroup.mem_comap]
    have : π (-1) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_center_iff]
      intro g
      rw [mul_neg, neg_mul, mul_one, one_mul]
    rw [this]
    exact one_mem _
  have htr : ∀ γ ∈ Γpm, ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) := by
    intro γ hγ
    rw [Subgroup.mem_comap, Subgroup.mem_map] at hγ
    obtain ⟨γ', hγ', hππ⟩ := hγ
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hππ
    have hz := eq_one_or_eq_neg_one_of_mem_center hππ
    have hγeq : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (γ : Matrix (Fin 2) (Fin 2) ℤ).trace =
          ε * ((⟨γ', hγ'⟩ : ↥(GammaH L H')) : SL(2, ℤ)).val.trace := by
      rcases hz with hz | hz
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [inv_mul_eq_one] at hz
        subst hz
        rw [one_mul]
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [inv_mul_eq_iff_eq_mul] at hz
        rw [hz, coe_mul, coe_neg, coe_one, mul_neg, mul_one, Matrix.trace_neg, neg_one_mul]
    obtain ⟨ε, hε, htrε⟩ := hγeq
    rw [htrε]
    exact ⟨trace_ne L H' r hrL hr hH' _ ε hε 0 (Or.inl rfl),
      trace_ne L H' r hrL hr hH' _ ε hε 1 (Or.inr (Or.inl rfl)),
      trace_ne L H' r hrL hr hH' _ ε hε (-1) (Or.inr (Or.inr rfl))⟩
  obtain ⟨b⟩ :=
    Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne
      Γpm hneg htr
  have hfree : IsFreeGroup ↥(Γpm.map π) := b.isFreeGroup
  have hmap : Γpm.map π = Γ'.map π :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

  have hinj : Function.Injective (π.comp Γ'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro γ hγ
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hγ
    rcases eq_one_or_eq_neg_one_of_mem_center hγ with h1 | h1
    · exact Subtype.ext h1
    · exact absurd (h1 ▸ γ.2) (neg_one_notMem L H' r hrL hr hH')
  have hrange : (π.comp Γ'.subtype).range = Γ'.map π := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  let e : ↥Γ' ≃* ↥(Γpm.map π) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hrange.trans hmap.symm))
  exact IsFreeGroup.ofMulEquiv e.symm

end Free

section Range

variable {L : ℕ} [NeZero L] {H H' : Subgroup (ZMod L)ˣ} (h : LevelLE L L H' H 1)

theorem coe_iotaDeg_one (γ : ↥(GammaH L H)) :
    ((iotaDeg L L H' H 1 h γ : ↥(GammaH L H')) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  show (conjLowerMat 1 (γ : SL(2, ℤ)) (h.dvd_entry γ)) i j = (γ : SL(2, ℤ)) i j
  fin_cases i <;> fin_cases j <;> simp [conjLowerMat]

theorem mem_range_iotaDeg_one_iff (γ' : ↥(GammaH L H')) :
    γ' ∈ (iotaDeg L L H' H 1 h).range ↔ (γ' : SL(2, ℤ)) ∈ GammaH L H := by
  constructor
  · rintro ⟨γ, rfl⟩
    rw [coe_iotaDeg_one]
    exact γ.2
  · intro hγ
    exact ⟨⟨γ', hγ⟩, Subtype.ext (coe_iotaDeg_one h ⟨γ', hγ⟩)⟩

def unitsChar (L : ℕ) (H' : Subgroup (ZMod L)ˣ) : ↥(GammaH L H') →* (ZMod L)ˣ :=
  (gamma0Units L).comp (Subgroup.inclusion (GammaH_le_Gamma0 H'))

theorem mem_GammaH_iff_unitsChar (γ' : ↥(GammaH L H')) :
    (γ' : SL(2, ℤ)) ∈ GammaH L H ↔ unitsChar L H' γ' ∈ H := by
  rw [mem_GammaH_iff]
  constructor
  · rintro ⟨_, hu⟩; exact hu
  · intro hu; exact ⟨GammaH_le_Gamma0 H' γ'.2, hu⟩

theorem mem_range_iff_unitsChar (γ' : ↥(GammaH L H')) :
    γ' ∈ (iotaDeg L L H' H 1 h).range ↔ unitsChar L H' γ' ∈ H := by
  rw [mem_range_iotaDeg_one_iff, mem_GammaH_iff_unitsChar]

scoped instance range_normal : ((iotaDeg L L H' H 1 h).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_range_iff_unitsChar] at hn ⊢
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  exact hn

theorem commutator_mem_range (x y : ↥(GammaH L H')) :
    x * y * x⁻¹ * y⁻¹ ∈ (iotaDeg L L H' H 1 h).range := by
  rw [mem_range_iff_unitsChar, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm,
    mul_inv_cancel]
  exact one_mem H

end Range

section Transport

variable {L : ℕ} [NeZero L] {H H' : Subgroup (ZMod L)ˣ} (h : LevelLE L L H' H 1)
  (A : Type*) [AddCommGroup A]

noncomputable abbrev iotaEquiv : ↥(GammaH L H) ≃* ↥((iotaDeg L L H' H 1 h).range) :=
  MonoidHom.ofInjective (iotaDeg_injective L L H' H 1 h)

noncomputable def pullChar (χ : ↥((iotaDeg L L H' H 1 h).range) →* Multiplicative A) : H1 L H A :=
  (MonoidHom.toAdditiveLeft χ).comp (MonoidHom.toAdditive (iotaEquiv h).toMonoidHom)

theorem pullChar_apply (χ : ↥((iotaDeg L L H' H 1 h).range) →* Multiplicative A)
    (γ : ↥(GammaH L H)) :
    pullChar h A χ (Additive.ofMul γ) = (χ (iotaEquiv h γ)).toAdd := rfl

theorem toMultiplicativeRight_pushChar_pullChar
    (χ : ↥((iotaDeg L L H' H 1 h).range) →* Multiplicative A) :
    AddMonoidHom.toMultiplicativeRight (pushChar L L H' H 1 A h (pullChar h A χ)) = χ := by
  ext x
  simp only [AddMonoidHom.toMultiplicativeRight_apply_apply, pushChar, AddMonoidHom.coe_comp,
    Function.comp_apply]
  rw [MonoidHom.toAdditive_apply_apply, pullChar_apply, MulEquiv.coe_toMonoidHom, toMul_ofMul,
    MulEquiv.apply_symm_apply, ofAdd_toAdd]

theorem pullChar_toMultiplicativeRight_pushChar (φ : H1 L H A) :
    pullChar h A (AddMonoidHom.toMultiplicativeRight (pushChar L L H' H 1 A h φ)) = φ := by
  refine AddMonoidHom.ext fun a => ?_
  change pullChar h A _ (Additive.ofMul (Additive.toMul a)) = φ (Additive.ofMul (Additive.toMul a))
  rw [pullChar_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, pushChar,
    AddMonoidHom.coe_comp, Function.comp_apply, MonoidHom.toAdditive_apply_apply,
    MulEquiv.coe_toMonoidHom, toMul_ofMul, MulEquiv.symm_apply_apply]

theorem pullChar_mul (χ₁ χ₂ : ↥((iotaDeg L L H' H 1 h).range) →* Multiplicative A) :
    pullChar h A (χ₁ * χ₂) = pullChar h A χ₁ + pullChar h A χ₂ :=
  AddMonoidHom.ext fun _ => rfl

theorem pullChar_one : pullChar h A (1 : ↥((iotaDeg L L H' H 1 h).range) →* Multiplicative A) = 0 :=
  AddMonoidHom.ext fun _ => rfl

theorem pullChar_inv (χ : ↥((iotaDeg L L H' H 1 h).range) →* Multiplicative A) :
    pullChar h A χ⁻¹ = -pullChar h A χ :=
  AddMonoidHom.ext fun _ => rfl

theorem pullChar_comp_conj (χ : ↥((iotaDeg L L H' H 1 h).range) →* Multiplicative A)
    (g : ↥(GammaH L H')) :
    pullChar h A (χ.comp (MulAut.conjNormal g : MulAut ↥((iotaDeg L L H' H 1 h).range)).toMonoidHom) =
      diamondRaw L H A ⟨(g : SL(2, ℤ)), GammaH_le_Gamma0 H' g.2⟩ (pullChar h A χ) := by
  refine AddMonoidHom.ext fun a => ?_
  set γ := Additive.toMul a
  change pullChar h A _ (Additive.ofMul γ) = diamondRaw L H A _ (pullChar h A χ) (Additive.ofMul γ)
  rw [pullChar_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  show _ = pullChar h A χ (Additive.ofMul (conjHom L H ⟨(g : SL(2, ℤ)), GammaH_le_Gamma0 H' g.2⟩
    (Additive.toMul (Additive.ofMul γ))))
  rw [toMul_ofMul, pullChar_apply]
  congr 2
  apply Subtype.ext
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
  show (g : SL(2, ℤ)) * ((iotaEquiv h γ : ↥((iotaDeg L L H' H 1 h).range)) : ↥(GammaH L H')) *
      (g : SL(2, ℤ))⁻¹ = ((iotaEquiv h (conjHom L H _ γ) : ↥((iotaDeg L L H' H 1 h).range)) :
        ↥(GammaH L H'))
  rw [MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply, coe_iotaDeg_one, coe_iotaDeg_one]
  rfl

theorem jDeg_eq (φ : H1 L H A) :
    jDeg L L H' H 1 A h φ = MonoidHom.toAdditiveLeft (MonoidHom.transfer
      (AddMonoidHom.toMultiplicativeRight (pushChar L L H' H 1 A h φ))) := rfl

end Transport

end GammaHDescentSol
p2m_reactivate "P2MW.S_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le.GammaHDescentSol"

open GammaHDescentSol CohCarrier in
theorem solution
    (L : ℕ) [NeZero L] (A : Type*) [AddCommGroup A]
    (H H' : Subgroup (ZMod L)ˣ) (h : CohCarrier.LevelLE L L H' H 1)
    (r : ℕ) (hrL : r ∣ L) (hr : 4 ≤ r)
    (hH' : ∀ u ∈ H', ZMod.castHom hrL (ZMod r) (u : ZMod L) = 1) :
    Function.Surjective (CohCarrier.jDeg L L H' H 1 A h) ∧
    ∀ φ : CohCarrier.H1 L H A, CohCarrier.jDeg L L H' H 1 A h φ = 0 ↔
      φ ∈ AddSubgroup.closure {y : CohCarrier.H1 L H A |
        ∃ σ : ↥(CongruenceSubgroup.Gamma0 L), (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH L H' ∧
          ∃ x : CohCarrier.H1 L H A, y = CohCarrier.diamondRaw L H A σ x - x} := by
  haveI : IsFreeGroup ↥(GammaH L H') := isFreeGroup_GammaH L H' r hrL hr hH'
  set R : Subgroup ↥(GammaH L H') := (iotaDeg L L H' H 1 h).range with hRdef
  obtain ⟨hsurj, hker⟩ :=
    IsFreeGroup.surjective_transfer_and_transfer_eq_one_iff_mem_closure R
      (commutator_mem_range h) (Multiplicative A)
  refine ⟨fun ψ => ?_, fun φ => ?_⟩
  ·
    obtain ⟨χ, hχ⟩ := hsurj (AddMonoidHom.toMultiplicativeRight ψ)
    refine ⟨pullChar h A χ, ?_⟩
    rw [jDeg_eq, toMultiplicativeRight_pushChar_pullChar]
    change MonoidHom.toAdditiveLeft (MonoidHom.transfer χ) = ψ
    rw [show MonoidHom.transfer χ = AddMonoidHom.toMultiplicativeRight ψ from hχ]
    exact AddMonoidHom.toMultiplicativeRight.symm_apply_apply ψ
  ·
    constructor
    · intro hφ
      set χ := AddMonoidHom.toMultiplicativeRight (pushChar L L H' H 1 A h φ) with hχdef
      have h1 : MonoidHom.transfer χ = 1 := by
        rw [jDeg_eq] at hφ
        have := congrArg AddMonoidHom.toMultiplicativeRight hφ
        rw [MonoidHom.toAdditiveLeft, Equiv.apply_symm_apply] at this
        rw [← hχdef] at this
        rw [this]
        rfl
      have hmem := (hker χ).mp h1
      rw [← pullChar_toMultiplicativeRight_pushChar h A φ, ← hχdef]
      refine Subgroup.closure_induction (p := fun χ _ => pullChar h A χ ∈ _) ?_ ?_ ?_ ?_ hmem
      · rintro ψ ⟨g, χ', rfl⟩
        rw [div_eq_mul_inv, pullChar_mul, pullChar_inv, pullChar_comp_conj, ← sub_eq_add_neg]
        exact AddSubgroup.subset_closure ⟨⟨(g : SL(2, ℤ)), GammaH_le_Gamma0 H' g.2⟩, g.2,
          pullChar h A χ', rfl⟩
      · show pullChar h A 1 ∈ _
        rw [pullChar_one]; exact zero_mem _
      · intro x y _ _ hx hy
        show pullChar h A (x * y) ∈ _
        rw [pullChar_mul]; exact add_mem hx hy
      · intro x _ hx
        show pullChar h A x⁻¹ ∈ _
        rw [pullChar_inv]; exact neg_mem hx
    · intro hφ

      refine (AddSubgroup.closure_le ((jDeg L L H' H 1 A h).ker)).mpr ?_ hφ
      rintro y ⟨σ, hσ, x, rfl⟩
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, sub_eq_zero]

      set χ := AddMonoidHom.toMultiplicativeRight (pushChar L L H' H 1 A h x) with hχdef
      have hx : x = pullChar h A χ := (pullChar_toMultiplicativeRight_pushChar h A x).symm
      have hconj : diamondRaw L H A σ x = pullChar h A
          (χ.comp (MulAut.conjNormal (⟨(σ : SL(2, ℤ)), hσ⟩ : ↥(GammaH L H')) :
            MulAut ↥((iotaDeg L L H' H 1 h).range)).toMonoidHom) := by
        rw [pullChar_comp_conj, ← hx]
      rw [hconj, jDeg_eq, jDeg_eq, toMultiplicativeRight_pushChar_pullChar, ← hχdef]
      congr 1

      have hgen := (hker ((χ.comp (MulAut.conjNormal (⟨(σ : SL(2, ℤ)), hσ⟩ : ↥(GammaH L H')) :
            MulAut ↥((iotaDeg L L H' H 1 h).range)).toMonoidHom) / χ)).mpr
        (Subgroup.subset_closure ⟨⟨(σ : SL(2, ℤ)), hσ⟩, χ, rfl⟩)

      have hmul : ∀ χ₁ χ₂ : ↥R →* Multiplicative A,
          MonoidHom.transfer (χ₁ * χ₂) = MonoidHom.transfer χ₁ * MonoidHom.transfer χ₂ := by
        intro χ₁ χ₂
        ext g
        rw [MonoidHom.mul_apply, MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default,
          MonoidHom.transfer_def _ default]
        simp only [Subgroup.leftTransversals.diff, MonoidHom.mul_apply, Finset.prod_mul_distrib]
      have := hmul ((χ.comp (MulAut.conjNormal (⟨(σ : SL(2, ℤ)), hσ⟩ : ↥(GammaH L H')) :
            MulAut ↥((iotaDeg L L H' H 1 h).range)).toMonoidHom) / χ) χ
      rw [div_mul_cancel, hgen, one_mul] at this
      exact this

end S_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le
end P2MW
export P2MW.S_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le (solution)
