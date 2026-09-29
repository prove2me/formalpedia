-- Prove2me | solution 1 for CohCarrier.jDeg_iDeg_four_identities_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ef2f03d4-1167-500f-91fa-8ee32f0553a5

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_jDeg_comp_iDegP_self
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_dvd
import Theorems.Thm_CohCarrier_coresAdd_comp_inclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_iDeg_four_identities_of_dvd

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace FourIdentitiesDvdSol

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {N q : ℕ} [NeZero N] [NeZero q]
  (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
  (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)

theorem coe_iotaDeg_one' (γ : ↥(GammaH (N * q) ⊤)) :
    ((iotaDeg N (N * q) ⊤ ⊤ 1 h1 γ : ↥(GammaH N ⊤)) : SL(2, ℤ)) = (γ : SL(2, ℤ)) :=
  coe_iotaDeg_one h1 γ

theorem iotaDeg_q_apply_01 (γ : ↥(GammaH (N * q) ⊤)) :
    ((iotaDeg N (N * q) ⊤ ⊤ q hq' γ : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 1 = (γ : SL(2, ℤ)) 0 1 * q := by
  simp [iotaDeg, conjLowerMat]

theorem mem_GammaH_top_iff (M : ℕ) (A : SL(2, ℤ)) : A ∈ GammaH M ⊤ ↔ A ∈ Gamma0 M := by
  rw [GammaH_top]

theorem range_iotaDeg_one_eq :
    (iotaDeg N (N * q) ⊤ ⊤ 1 h1).range = GammaHLower N ⊤ q := by
  ext k
  rw [GammaHLower, Subgroup.mem_subgroupOf, Gamma0_mem, mul_comm q N]
  constructor
  · rintro ⟨γ, rfl⟩
    rw [coe_iotaDeg_one' h1 γ]
    exact Gamma0_mem.mp ((mem_GammaH_top_iff _ _).mp γ.2)
  · intro hk
    have hk' : (k : SL(2, ℤ)) ∈ GammaH (N * q) ⊤ := (mem_GammaH_top_iff _ _).mpr (Gamma0_mem.mpr hk)
    refine ⟨⟨(k : SL(2, ℤ)), hk'⟩, Subtype.ext ?_⟩
    exact coe_iotaDeg_one' h1 _

theorem range_iotaDeg_q_eq :
    (iotaDeg N (N * q) ⊤ ⊤ q hq').range = GammaHUpper N ⊤ q := by
  ext k
  rw [GammaHUpper, Subgroup.mem_subgroupOf, mem_Gamma0Upper]
  constructor
  · rintro ⟨γ, rfl⟩
    rw [iotaDeg_q_apply_01 hq' γ]
    push_cast
    rw [ZMod.natCast_self, mul_zero]
  · intro hk
    have hb : (q : ℤ) ∣ (k : SL(2, ℤ)) 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hk

    set A : SL(2, ℤ) := conjUpperMat q (k : SL(2, ℤ)) hb with hAdef
    have hk0 : ((k : ↥(GammaH N ⊤)) : SL(2, ℤ)) ∈ Gamma0 N := (mem_GammaH_top_iff _ _).mp k.2
    have hA0 : A ∈ Gamma0 (N * q) := by
      rw [Gamma0_mem]
      have : A 1 0 = (k : SL(2, ℤ)) 1 0 * q := by simp [hAdef, conjUpperMat]
      rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact mul_dvd_mul_right ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hk0)) _
    have hA : A ∈ GammaH (N * q) ⊤ := (mem_GammaH_top_iff _ _).mpr hA0
    have hc : (q : ℤ) ∣ (conjUpperMat q (k : SL(2, ℤ)) hb) 1 0 := by
      rw [conjUpperMat_apply_10]; exact dvd_mul_left _ _
    refine ⟨⟨A, hA⟩, Subtype.ext ?_⟩
    exact conjLowerMat_conjUpperMat q (k : SL(2, ℤ)) hb hc

def lMat (t : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; t, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem lMat_apply_00 (t : ℤ) : (lMat t) 0 0 = 1 := rfl
@[scoped simp] theorem lMat_apply_01 (t : ℤ) : (lMat t) 0 1 = 0 := rfl
@[scoped simp] theorem lMat_apply_10 (t : ℤ) : (lMat t) 1 0 = t := rfl
@[scoped simp] theorem lMat_apply_11 (t : ℤ) : (lMat t) 1 1 = 1 := rfl

variable (N) in

theorem lMat_mem_GammaH (t : ℤ) : lMat (N * t) ∈ GammaH N ⊤ := by
  rw [mem_GammaH_top_iff, Gamma0_mem]
  show (((N : ℤ) * t : ℤ) : ZMod N) = 0
  push_cast
  rw [ZMod.natCast_self, zero_mul]

variable (N) in

def lElt (t : ℤ) : ↥(GammaH N ⊤) := ⟨lMat (N * t), lMat_mem_GammaH N t⟩

@[scoped simp] theorem coe_lElt (t : ℤ) : ((lElt N t : ↥(GammaH N ⊤)) : SL(2, ℤ)) = lMat (N * t) := rfl

theorem mul_inv_apply_10 (x y : SL(2, ℤ)) :
    (x * y⁻¹ : SL(2, ℤ)) 1 0 = x 1 0 * y 1 1 - x 1 1 * y 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem rightRel_lower_mk_eq_mk_iff (x y : ↥(GammaH N ⊤)) :
    (Quotient.mk'' x : Quotient (QuotientGroup.rightRel (GammaHLower N ⊤ q))) = Quotient.mk'' y ↔
      ((((y : SL(2, ℤ)) * (x : SL(2, ℤ))⁻¹) 1 0 : ℤ) : ZMod (q * N)) = 0 := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, Gamma0_mem,
    Subgroup.coe_mul, Subgroup.coe_inv]

theorem exists_c_eq (γ : ↥(GammaH N ⊤)) : ∃ c₀ : ℤ, (γ : SL(2, ℤ)) 1 0 = N * c₀ := by
  have h : (γ : SL(2, ℤ)) ∈ Gamma0 N := (mem_GammaH_top_iff _ _).mp γ.2
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact h

theorem cast_N_mul_eq_zero_iff (x : ℤ) :
    (((N : ℤ) * x : ℤ) : ZMod (q * N)) = 0 ↔ ((x : ℤ) : ZMod q) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  push_cast
  rw [mul_comm (q : ℤ) (N : ℤ)]
  exact Int.mul_dvd_mul_iff_left hN

noncomputable def rightQuotLowerEquivOfDvd (hqN : q ∣ N) :
    ZMod q ≃ Quotient (QuotientGroup.rightRel (GammaHLower N ⊤ q)) := by
  refine Equiv.ofBijective (fun j => Quotient.mk'' (lElt N (j.val : ℤ))) ⟨?_, ?_⟩
  · intro j j' h
    rw [rightRel_lower_mk_eq_mk_iff, mul_inv_apply_10] at h
    simp only [coe_lElt, lMat_apply_10, lMat_apply_11, mul_one, one_mul] at h
    rw [← mul_sub, cast_N_mul_eq_zero_iff] at h
    push_cast at h
    simp only [ZMod.natCast_zmod_val] at h
    linear_combination -h
  · intro c
    induction c using Quotient.inductionOn' with
    | h g =>
      obtain ⟨c₀, hc₀⟩ := exists_c_eq g
      have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
      rw [Matrix.det_fin_two, hc₀] at hdet

      have had : ((((g : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) * ((((g : SL(2, ℤ)) 1 1 : ℤ)) : ZMod q) = 1 := by
        have h := congrArg (Int.cast : ℤ → ZMod q) hdet
        push_cast at h
        rw [(ZMod.natCast_eq_zero_iff N q).mpr hqN] at h
        linear_combination h
      refine ⟨(c₀ : ZMod q) * ((((g : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q), ?_⟩
      show (Quotient.mk'' (lElt N (((c₀ : ZMod q) * ((((g : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q)).val : ℤ)) :
          Quotient (QuotientGroup.rightRel (GammaHLower N ⊤ q))) = Quotient.mk'' g
      rw [rightRel_lower_mk_eq_mk_iff, mul_inv_apply_10]
      simp only [coe_lElt, lMat_apply_10, lMat_apply_11, mul_one]
      have key : ∀ (a v : ℤ), (N : ℤ) * c₀ - a * ((N : ℤ) * v) = (N : ℤ) * (c₀ - a * v) :=
        fun a v => by ring
      rw [hc₀, key, cast_N_mul_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination (-(c₀ : ZMod q)) * had

theorem index_GammaHLower_of_dvd (hqN : q ∣ N) : (GammaHLower N ⊤ q).index = q := by
  rw [Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _),
    ← Nat.card_congr (rightQuotLowerEquivOfDvd (N := N) hqN), Nat.card_zmod]

variable {A : Type} [AddCommGroup A]

theorem range_iotaDeg_one_le : (iotaDeg N (N * q) ⊤ ⊤ 1 h1).range ≤ GammaHLower N ⊤ q :=
  (range_iotaDeg_one_eq h1).le

theorem pushChar_one_iDeg_q_eq (φ : H1 N ⊤ A) :
    pushChar N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ q A hq' φ)
      = (φ.comp (conjLowerL N ⊤ q).toAdditive).comp
          (Subgroup.inclusion (range_iotaDeg_one_le (q := q) h1)).toAdditive := by
  refine AddMonoidHom.ext fun a => ?_
  set x : ↥((iotaDeg N (N * q) ⊤ ⊤ 1 h1).range) := Additive.toMul a with hx
  set γ' : ↥(GammaH (N * q) ⊤) :=
    ((iotaDeg N (N * q) ⊤ ⊤ 1 h1).ofInjective (iotaDeg_injective N (N * q) ⊤ ⊤ 1 h1)).symm x with hγ'
  have hιγ' : iotaDeg N (N * q) ⊤ ⊤ 1 h1 γ' = (x : ↥(GammaH N ⊤)) :=
    MonoidHom.apply_ofInjective_symm (iotaDeg_injective N (N * q) ⊤ ⊤ 1 h1) x
  have hcoe : (γ' : SL(2, ℤ)) = ((x : ↥(GammaH N ⊤)) : SL(2, ℤ)) := by
    rw [← coe_iotaDeg_one' h1 γ', hιγ']

  show φ (Additive.ofMul (iotaDeg N (N * q) ⊤ ⊤ q hq' γ')) =
    φ (Additive.ofMul (conjLowerL N ⊤ q ⟨(x : ↥(GammaH N ⊤)), range_iotaDeg_one_le h1 x.2⟩))
  congr 2
  apply Subtype.ext
  have key : ∀ (B C : SL(2, ℤ)) (hB : (q : ℤ) ∣ B 1 0) (hC : (q : ℤ) ∣ C 1 0), B = C →
      conjLowerMat q B hB = conjLowerMat q C hC := by
    rintro B C hB hC rfl; rfl
  exact key _ _ (hq'.dvd_entry γ')
    (dvd_of_mem_GammaHLower N ⊤ q ⟨_, range_iotaDeg_one_le h1 x.2⟩) hcoe

theorem coresAdd_conjLowerL_eq (φ : H1 N ⊤ A) :
    coresAdd (GammaHLower N ⊤ q) (φ.comp (conjLowerL N ⊤ q).toAdditive) = heckeTlower N ⊤ q A φ :=
  rfl

theorem jDeg_one_iDeg_one (hqN : q ∣ N) (φ : H1 N ⊤ A) :
    jDeg N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ 1 A h1 φ) = q • φ := by
  rw [jDeg_comp_iDegP_self h1 φ, range_iotaDeg_one_eq h1, index_GammaHLower_of_dvd hqN]

theorem jDeg_q_iDeg_q (hqN : q ∣ N) (φ : H1 N ⊤ A) :
    jDeg N (N * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ q A hq' φ) = q • φ := by
  rw [jDeg_comp_iDegP_self hq' φ, range_iotaDeg_q_eq hq', index_GammaHUpper_of_dvd N ⊤ q hqN]

theorem jDeg_q_iDeg_one (φ : H1 N ⊤ A) :
    jDeg N (N * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ 1 A h1 φ) = heckeT N ⊤ q A φ := by
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact NeZero.ne q⟩
  rw [jDeg_iDeg_cross_eq_index_smul_heckeT q hq' h1 (dvd_refl _) (one_mul q).symm φ,
    range_iotaDeg_q_eq hq', Subgroup.subgroupOf_self, Subgroup.index_top, one_smul]

theorem jDeg_one_iDeg_q (φ : H1 N ⊤ A) :
    jDeg N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ q A hq' φ) = heckeTlower N ⊤ q A φ := by
  have hidx : (((iotaDeg N (N * q) ⊤ ⊤ 1 h1).range).subgroupOf (GammaHLower N ⊤ q)).index = 1 := by
    rw [range_iotaDeg_one_eq h1, Subgroup.subgroupOf_self, Subgroup.index_top]
  show coresAdd _ (pushChar N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ q A hq' φ)) = _
  rw [pushChar_one_iDeg_q_eq h1 hq' φ,
    coresAdd_comp_inclusion _ _ (range_iotaDeg_one_le (q := q) h1), hidx, one_smul,
    coresAdd_conjLowerL_eq]

end FourIdentitiesDvdSol
p2m_reactivate "P2MW.S_CohCarrier_jDeg_iDeg_four_identities_of_dvd.FourIdentitiesDvdSol"

open CohCarrier in
theorem solution (N q : ℕ) [NeZero N] [NeZero q] (A : Type) [AddCommGroup A] (hqN : q ∣ N)
    (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q) :
    (∀ φ, jDeg N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ 1 A h1 φ) = q • φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ q A hq' φ) = q • φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ 1 A h1 φ) = heckeT N ⊤ q A φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ q A hq' φ) = heckeTlower N ⊤ q A φ) :=
  ⟨FourIdentitiesDvdSol.jDeg_one_iDeg_one h1 hqN, FourIdentitiesDvdSol.jDeg_q_iDeg_q hq' hqN,
    FourIdentitiesDvdSol.jDeg_q_iDeg_one h1 hq', FourIdentitiesDvdSol.jDeg_one_iDeg_q h1 hq'⟩

end
p2m_reactivate "P2MW.S_CohCarrier_jDeg_iDeg_four_identities_of_dvd.FourIdentitiesDvdSol"

end S_CohCarrier_jDeg_iDeg_four_identities_of_dvd
end P2MW
export P2MW.S_CohCarrier_jDeg_iDeg_four_identities_of_dvd (solution)
