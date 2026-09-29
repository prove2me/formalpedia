-- Prove2me | solution 1 for CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeTlower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5dc6665d-3dfd-56d6-9f4f-641de0dbb528

import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_coresAdd_comp_inclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace IharaMintBL

open CohCarrier

variable {M M' d d' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
  {A : Type*} [AddCommGroup A]

theorem pushChar_iDeg_cross_impl [NeZero d] [NeZero d'] (h : LevelLE M M' H H' d)
    (h' : LevelLE M M' H H' d') (φ : H1 M H A) (x : Additive ↥(iotaDeg M M' H H' d h).range) :
    pushChar M M' H H' d A h ((iDeg' M M' H H' d' A h') φ) x
      = φ (Additive.ofMul ((iotaDeg M M' H H' d' h')
          (((iotaDeg M M' H H' d h).ofInjective
            (iotaDeg_injective M M' H H' d h)).symm (Additive.toMul x)))) := rfl

theorem conjLowerMat_conjLowerMat_impl (q d : ℕ) [NeZero q] [NeZero d] (γ : SL(2, ℤ))
    (hd : (d : ℤ) ∣ γ 1 0) (hdq : ((d * q : ℕ) : ℤ) ∣ γ 1 0) :
    conjLowerMat q (conjLowerMat d γ hd)
        (by show (q : ℤ) ∣ γ 1 0 / (d : ℤ)
            obtain ⟨k, hk⟩ := hdq; push_cast at hk
            rw [hk, mul_assoc,
              Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne d))]; exact ⟨k, rfl⟩)
      = conjLowerMat (d * q) γ (by push_cast at hdq ⊢; exact hdq) := by
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hd0 : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
  · rfl
  · push_cast; ring
  · obtain ⟨k, hk⟩ := hdq; push_cast at hk ⊢
    rw [hk, mul_assoc, Int.mul_ediv_cancel_left _ hd0,
      Int.mul_ediv_cancel_left _ hq0,
      ← mul_assoc, Int.mul_ediv_cancel_left _ (mul_ne_zero hd0 hq0)]
  · rfl

theorem range_iotaDeg_le_GammaHLower_impl (q : ℕ) [NeZero d] (hcop : Nat.Coprime q M)
    (h : LevelLE M M' H H' d) (hdqM' : ((d * q : ℕ) : ℤ) ∣ (M' : ℤ)) :
    (iotaDeg M M' H H' d h).range ≤ GammaHLower M H q := by
  rintro k ⟨γ', rfl⟩
  rw [mem_GammaHLower_iff_of_coprime M H q hcop]
  show (q : ℤ) ∣ (((γ' : SL(2, ℤ)) 1 0) / (d : ℤ) : ℤ)
  have hM' : (M' : ℤ) ∣ (γ' : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (Gamma0_mem.mp (mem_GammaH_iff.mp (γ' : ↥(GammaH M' H')).2).1)
  obtain ⟨k, hk⟩ := hdqM'.trans hM'
  push_cast at hk
  rw [hk, mul_assoc, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne d))]
  exact ⟨k, rfl⟩

theorem pushChar_iDeg_eq_conjLowerL_inclusion_impl (q : ℕ) [NeZero q] [NeZero d] [NeZero d']
    [NeZero M'] (hcop : Nat.Coprime q M)
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
    (hdqM' : ((d * q : ℕ) : ℤ) ∣ (M' : ℤ)) (hdiv : d' = d * q) (φ : H1 M H A) :
    pushChar M M' H H' d A h ((iDeg' M M' H H' d' A h') φ)
      = (φ.comp (conjLowerL M H q).toAdditive).comp
          (Subgroup.inclusion (range_iotaDeg_le_GammaHLower_impl q hcop h hdqM')).toAdditive := by
  subst hdiv
  refine AddMonoidHom.ext fun x => ?_
  rw [pushChar_iDeg_cross_impl h h' φ x]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, MonoidHom.toAdditive_apply_apply]
  set γ' := (MonoidHom.ofInjective (iotaDeg_injective M M' H H' d h)).symm
    (Additive.toMul x) with hγ'
  have hk : (iotaDeg M M' H H' d h γ' : ↥(GammaH M H))
      = (Additive.toMul x : ↥(iotaDeg M M' H H' d h).range) := by
    rw [hγ', MonoidHom.apply_ofInjective_symm]
  refine congrArg (φ ∘ Additive.ofMul) (Subtype.ext ?_)
  show (conjLowerMat (d * q) (γ' : SL(2, ℤ)) (h'.dvd_entry γ') : SL(2, ℤ))
    = (conjLowerMat q ((↑(Additive.toMul x) : ↥(GammaH M H)) : SL(2, ℤ))
        (dvd_of_mem_GammaHLower M H q
          (Subgroup.inclusion (range_iotaDeg_le_GammaHLower_impl q hcop h hdqM')
            (Additive.toMul x))) : SL(2, ℤ))
  simp only [← hk]
  exact (conjLowerMat_conjLowerMat_impl q d (γ' : SL(2, ℤ)) (h.dvd_entry γ')
    (by push_cast; exact_mod_cast (h'.dvd_entry γ'))).symm

end IharaMintBL

open CohCarrier IharaMintBL in
theorem solution {M : ℕ} {H : Subgroup (ZMod M)ˣ}
    {q : ℕ} {A : Type} [AddCommGroup A] {M' d d' : ℕ} {H' : Subgroup (ZMod M')ˣ}
    [NeZero M] [NeZero q] [NeZero d] [NeZero d'] [NeZero M']
    (hq : q.Prime) (hqM : ¬ q ∣ M)
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
    (hdqM' : ((d * q : ℕ) : ℤ) ∣ (M' : ℤ)) (hdiv : d' = d * q) (φ : H1 M H A) :
    jDeg M M' H H' d A h (iDeg' M M' H H' d' A h' φ)
      = ((iotaDeg M M' H H' d h).range.subgroupOf (GammaHLower M H q)).index
          • heckeTlower M H q A φ := by
  have hcop : Nat.Coprime q M := (hq.coprime_iff_not_dvd).mpr hqM
  show coresAdd _ (pushChar M M' H H' d A h ((iDeg' M M' H H' d' A h') φ)) = _
  rw [pushChar_iDeg_eq_conjLowerL_inclusion_impl q hcop h h' hdqM' hdiv φ,
    CohCarrier.coresAdd_comp_inclusion _ _
      (range_iotaDeg_le_GammaHLower_impl q hcop h hdqM')]
  rfl

#print axioms solution

end S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower
end P2MW
export P2MW.S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower (solution)
