-- Prove2me | solution 1 for CohCarrier.index_range_iotaDeg_of_prime_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/020436d4-74c9-5625-b1df-74cde143dffb

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_comap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open CongruenceSubgroup
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "coe_iotaDeg_one GammaHLower mem_Gamma0Upper gamma0Units val_gamma0Units GammaH mem_GammaH_iff conjUpperMat conjUpperMat_apply_11 conjUpperMat_apply_10 GammaHUpper dvd_of_mem_GammaHUpper conjLowerMat LevelLE iotaDeg conjLowerMat_conjUpperMat index_GammaHUpper_of_prime"
namespace PreimageLevel
p2m_open "CohCarrier"

variable (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ)

abbrev preH : Subgroup (ZMod (N * q))ˣ := H.comap (ZMod.unitsMap (dvd_mul_right N q))

theorem range_iotaDeg_q (hq' : LevelLE N (N * q) H (preH N q H) q) :
    (iotaDeg N (N * q) H (preH N q H) q hq').range = GammaHUpper N H q := by
  ext γ
  constructor
  · rintro ⟨γ', rfl⟩
    rw [GammaHUpper, Subgroup.mem_subgroupOf, mem_Gamma0Upper]
    show ((((iotaDeg N (N * q) H (preH N q H) q hq' γ' : ↥(GammaH N H)) : SL(2, ℤ)) 0 1 : ℤ) : ZMod q) = 0
    simp [iotaDeg, conjLowerMat]
  · intro hγ
    have hb : (q : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := dvd_of_mem_GammaHUpper N H q ⟨γ, hγ⟩

    obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp γ.2
    have hmem : conjUpperMat q (γ : SL(2, ℤ)) hb ∈ GammaH (N * q) (preH N q H) := by
      rw [mem_GammaH_iff]
      refine ⟨?_, ?_⟩
      · rw [Gamma0_mem, conjUpperMat_apply_10]
        rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        exact mul_dvd_mul hγ0 (dvd_refl _)
      · rw [Subgroup.mem_comap]
        convert hγH using 1
        apply Units.ext
        rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, val_gamma0Units, val_gamma0Units]
        simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, conjUpperMat_apply_11, ZMod.castHom_apply]
        rw [ZMod.cast_intCast (dvd_mul_right N q)]
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    have hc : (q : ℤ) ∣ (conjUpperMat q (γ : SL(2, ℤ)) hb) 1 0 := by
      rw [conjUpperMat_apply_10]; exact dvd_mul_left _ _
    show conjLowerMat q (conjUpperMat q (γ : SL(2, ℤ)) hb) (hq'.dvd_entry ⟨_, hmem⟩) = _
    exact conjLowerMat_conjUpperMat q _ hb _

theorem range_iotaDeg_one (h1 : LevelLE N (N * q) H (preH N q H) 1) :
    (iotaDeg N (N * q) H (preH N q H) 1 h1).range = GammaHLower N H q := by
  ext γ
  rw [GammaHLower, Subgroup.mem_subgroupOf, Gamma0_mem]
  constructor
  · rintro ⟨γ', rfl⟩
    rw [coe_iotaDeg_one]
    have hγ0 : ((γ' : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 (N * q) := (mem_GammaH_iff.mp γ'.2).1
    rw [Gamma0_mem] at hγ0
    rw [mul_comm q N]
    exact hγ0
  · intro hc
    obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp γ.2
    have hmem : (γ : SL(2, ℤ)) ∈ GammaH (N * q) (preH N q H) := by
      rw [mem_GammaH_iff]
      refine ⟨by rw [Gamma0_mem, mul_comm N q]; exact hc, ?_⟩
      rw [Subgroup.mem_comap]
      convert hγH using 1
      apply Units.ext
      rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, val_gamma0Units, val_gamma0Units]
      simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, ZMod.castHom_apply]
      rw [ZMod.cast_intCast (dvd_mul_right N q)]
    exact ⟨⟨_, hmem⟩, Subtype.ext (coe_iotaDeg_one h1 _)⟩

theorem mul_inv_apply_10 (x y : SL(2, ℤ)) : (x * y⁻¹ : SL(2, ℤ)) 1 0 = x 1 0 * y 1 1 - x 1 1 * y 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem lower_mk_eq_mk_iff (x y : ↥(GammaH N H)) :
    (Quotient.mk'' x : Quotient (QuotientGroup.rightRel (GammaHLower N H q))) = Quotient.mk'' y ↔
      ((((y : SL(2, ℤ)) * (x : SL(2, ℤ))⁻¹) 1 0 : ℤ) : ZMod (q * N)) = 0 := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, Gamma0_mem, Subgroup.coe_mul, Subgroup.coe_inv]

def lMat (j : ℤ) : SL(2, ℤ) := ⟨!![1, 0; j * N, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem lMat_apply_00 (j : ℤ) : (lMat N j) 0 0 = 1 := rfl
@[scoped simp] theorem lMat_apply_01 (j : ℤ) : (lMat N j) 0 1 = 0 := rfl
@[scoped simp] theorem lMat_apply_10 (j : ℤ) : (lMat N j) 1 0 = j * N := rfl
@[scoped simp] theorem lMat_apply_11 (j : ℤ) : (lMat N j) 1 1 = 1 := rfl

theorem lMat_mem (j : ℤ) : lMat N j ∈ GammaH N H := by
  have h0 : lMat N j ∈ Gamma0 N := by
    rw [Gamma0_mem]; show (((j * N : ℤ)) : ZMod N) = 0; simp
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : gamma0Units N ⟨lMat N j, h0⟩ = 1 := by
    apply Units.ext; rw [val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod N) = 1; exact Int.cast_one
  rw [e]; exact H.one_mem

def lElt (j : ℤ) : ↥(GammaH N H) := ⟨lMat N j, lMat_mem N H j⟩
@[scoped simp] theorem coe_lElt (j : ℤ) : ((lElt N H j : ↥(GammaH N H)) : SL(2, ℤ)) = lMat N j := rfl

def xMat (hcop : Nat.Coprime N q) : SL(2, ℤ) :=
  ⟨!![1, -Nat.gcdA N q; N, (q : ℤ) * Nat.gcdB N q], by
    rw [Matrix.det_fin_two_of]
    have h := Nat.gcd_eq_gcd_ab N q
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    push_cast at h
    linear_combination -h⟩

@[scoped simp] theorem xMat_apply_00 (hcop : Nat.Coprime N q) : (xMat N q hcop) 0 0 = 1 := rfl
@[scoped simp] theorem xMat_apply_01 (hcop : Nat.Coprime N q) : (xMat N q hcop) 0 1 = -Nat.gcdA N q := rfl
@[scoped simp] theorem xMat_apply_10 (hcop : Nat.Coprime N q) : (xMat N q hcop) 1 0 = N := rfl
@[scoped simp] theorem xMat_apply_11 (hcop : Nat.Coprime N q) : (xMat N q hcop) 1 1 = (q : ℤ) * Nat.gcdB N q := rfl

theorem xMat_mem (hcop : Nat.Coprime N q) : xMat N q hcop ∈ GammaH N H := by
  have h0 : xMat N q hcop ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((N : ℤ) : ZMod N) = 0; simp
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : gamma0Units N ⟨xMat N q hcop, h0⟩ = 1 := by
    apply Units.ext; rw [val_gamma0Units, Units.val_one]
    show (((q : ℤ) * Nat.gcdB N q : ℤ) : ZMod N) = 1
    have h := Nat.gcd_eq_gcd_ab N q
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    have h' := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at h'
    rw [ZMod.natCast_self, zero_mul, zero_add] at h'
    push_cast
    exact h'.symm
  rw [e]; exact H.one_mem

def xElt (hcop : Nat.Coprime N q) : ↥(GammaH N H) := ⟨xMat N q hcop, xMat_mem N q H hcop⟩
@[scoped simp] theorem coe_xElt (hcop : Nat.Coprime N q) : ((xElt N q H hcop : ↥(GammaH N H)) : SL(2, ℤ)) = xMat N q hcop := rfl

variable [Fact q.Prime]

theorem lower_mk_eq_mk_xElt_iff (hcop : Nat.Coprime N q) (g : ↥(GammaH N H)) :
    (Quotient.mk'' g : Quotient (QuotientGroup.rightRel (GammaHLower N H q))) = Quotient.mk'' (xElt N q H hcop) ↔
      (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod q) = 0 := by
  have hq1 : q ≠ 1 := (Fact.out : q.Prime).ne_one
  rw [lower_mk_eq_mk_iff, mul_inv_apply_10]
  simp only [coe_xElt, xMat_apply_10, xMat_apply_11]

  obtain ⟨hg0, -⟩ := mem_GammaH_iff.mp g.2
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg0
  obtain ⟨c', hc'⟩ := hg0
  rw [hc', ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  constructor
  · rintro ⟨k, hk⟩

    have h2 : (N : ℤ) * ((g : SL(2, ℤ)) 1 1 - q * (Nat.gcdB N q * c' + k)) = 0 := by
      push_cast at hk; linear_combination hk
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hN0
    · exact ⟨Nat.gcdB N q * c' + k, by linear_combination h⟩
  · rintro ⟨k, hk⟩
    refine ⟨k - Nat.gcdB N q * c', ?_⟩
    push_cast
    rw [hk]
    ring

theorem lower_mk_eq_mk_lElt_iff (j : ℤ) (g : ↥(GammaH N H)) :
    (Quotient.mk'' g : Quotient (QuotientGroup.rightRel (GammaHLower N H q))) = Quotient.mk'' (lElt N H j) ↔
      (((j * N * (g : SL(2, ℤ)) 1 1 - (g : SL(2, ℤ)) 1 0 : ℤ)) : ZMod (q * N)) = 0 := by
  rw [lower_mk_eq_mk_iff, mul_inv_apply_10]
  simp only [coe_lElt, lMat_apply_10, lMat_apply_11, one_mul]

theorem index_GammaHLower_of_prime (hcop : Nat.Coprime N q) : (GammaHLower N H q).index = q + 1 := by
  classical
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N

  let f : Option (ZMod q) → Quotient (QuotientGroup.rightRel (GammaHLower N H q)) := fun o =>
    Option.casesOn o (Quotient.mk'' (xElt N q H hcop)) (fun j => Quotient.mk'' (lElt N H (j.val : ℤ)))

  have hl : ∀ (j : ℤ) (g : ↥(GammaH N H)) (c' : ℤ), (g : SL(2, ℤ)) 1 0 = N * c' →
      ((Quotient.mk'' g : Quotient (QuotientGroup.rightRel (GammaHLower N H q))) = Quotient.mk'' (lElt N H j) ↔
        ((j * (g : SL(2, ℤ)) 1 1 - c' : ℤ) : ZMod q) = 0) := by
    intro j g c' hc'
    rw [lower_mk_eq_mk_lElt_iff, hc', ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨k, hk⟩
      have h2 : (N : ℤ) * (j * (g : SL(2, ℤ)) 1 1 - c' - q * k) = 0 := by push_cast at hk; linear_combination hk
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hN0
      · exact ⟨k, by linear_combination h⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by push_cast; linear_combination (N : ℤ) * hk⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro (_ | j) (_ | j') h
      · rfl
      · exfalso
        have h' := (lower_mk_eq_mk_xElt_iff N q H hcop _).mp h.symm
        simp at h'
      · exfalso
        have h' := (lower_mk_eq_mk_xElt_iff N q H hcop _).mp h
        simp at h'
      · have h' := (hl (j'.val : ℤ) (lElt N H (j.val : ℤ)) (j.val : ℤ) (by simp [mul_comm])).mp h
        simp only [coe_lElt, lMat_apply_11, mul_one, Int.cast_sub, ZMod.intCast_cast, ZMod.natCast_val, ZMod.cast_id',
          id_eq, sub_eq_zero] at h'
        rw [h']
    · intro c
      induction c using Quotient.inductionOn' with
      | h g =>
        obtain ⟨hg0, -⟩ := mem_GammaH_iff.mp g.2
        rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg0
        obtain ⟨c', hc'⟩ := hg0
        by_cases h0 : (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod q) = 0
        · exact ⟨none, ((lower_mk_eq_mk_xElt_iff N q H hcop g).mpr h0).symm⟩
        · refine ⟨some ((c' : ZMod q) * (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod q)⁻¹), ?_⟩
          show (Quotient.mk'' (lElt N H _) : Quotient (QuotientGroup.rightRel (GammaHLower N H q))) = Quotient.mk'' g
          rw [eq_comm, hl _ g c' hc']
          push_cast
          simp only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id_eq]
          rw [inv_mul_cancel_right₀ (show (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod q) ≠ 0 from h0), sub_self]
  rw [Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (GammaHLower N H q)),
    ← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

end CohCarrier.PreimageLevel
p2m_reactivate "P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_comap.CohCarrier P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_comap.CohCarrier.PreimageLevel"
p2m_reactivate "P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_comap.CohCarrier"

open _root_.CohCarrier _root_.P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_comap.CohCarrier CohCarrier.PreimageLevel in

theorem solution (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (H : Subgroup (ZMod N)ˣ)
    (h₁ : LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1)
    (hq' : LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q) :
    (iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 h₁).range.index = q + 1 ∧
    (iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q hq').range.index = q + 1 ∧
    ((iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q hq').range.subgroupOf (GammaHUpper N H q)).index = 1 ∧
    ((iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 h₁).range.subgroupOf (GammaHLower N H q)).index = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : Nat.Coprime N q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm
  have e1 := range_iotaDeg_one N q H h₁
  have eq := range_iotaDeg_q N q H hq'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; exact index_GammaHLower_of_prime N q H hcop
  · rw [eq]; exact CohCarrier.index_GammaHUpper_of_prime N H q hq hqN
  · rw [eq, Subgroup.subgroupOf_self, Subgroup.index_top]
  · rw [e1, Subgroup.subgroupOf_self, Subgroup.index_top]

namespace CohCarrier p2m_export "CohCarrier" "coe_iotaDeg_one GammaHLower mem_Gamma0Upper gamma0Units val_gamma0Units GammaH mem_GammaH_iff conjUpperMat conjUpperMat_apply_11 conjUpperMat_apply_10 GammaHUpper dvd_of_mem_GammaHUpper conjLowerMat LevelLE iotaDeg conjLowerMat_conjUpperMat index_GammaHUpper_of_prime" end CohCarrier
p2m_open_scoped "CohCarrier" in
open _root_.CohCarrier _root_.P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_comap.CohCarrier in

theorem CohCarrier.levelLE_comap_one_and_q (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ) :
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 ∧
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q :=
  ⟨⟨dvd_mul_right N q, one_dvd _, fun u hu => hu⟩,
   ⟨dvd_mul_right N q, by rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne N))], fun u hu => hu⟩⟩

end S_CohCarrier_index_range_iotaDeg_of_prime_comap
end P2MW
export P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_comap (solution)
