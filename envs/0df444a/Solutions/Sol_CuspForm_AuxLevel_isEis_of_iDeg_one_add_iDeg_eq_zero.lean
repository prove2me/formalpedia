-- Prove2me | solution 1 for CuspForm.AuxLevel.isEis_of_iDeg_one_add_iDeg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/084b1270-5367-562c-97c8-32ffced295e9

import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CuspForm_AuxLevelHeckeModule
import Theorems.Thm_CohCarrier_isEis_kernel_pair_of_prime
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_AuxLevel_isEis_of_iDeg_one_add_iDeg_eq_zero
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply"

set_option autoImplicit false

namespace IharaAux

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable (N r : ℕ)

theorem gammaH_le_top : GammaH (N * r) (CuspForm.AuxLevel.subgroup N r) ≤ GammaH (N * r) ⊤ := by
  intro γ hγ
  obtain ⟨h0, -⟩ := mem_GammaH_iff.mp hγ
  exact mem_GammaH_iff.mpr ⟨h0, Subgroup.mem_top _⟩

def incl : ↥(GammaH (N * r) (CuspForm.AuxLevel.subgroup N r)) →* ↥(GammaH (N * r) ⊤) :=
  Subgroup.inclusion (gammaH_le_top N r)

@[scoped simp] theorem coe_incl (δ : ↥(GammaH (N * r) (CuspForm.AuxLevel.subgroup N r))) :
    ((incl N r δ : ↥(GammaH (N * r) ⊤)) : SL(2, ℤ)) = (δ : SL(2, ℤ)) := rfl

theorem levelLE_top_one : LevelLE N (N * r) ⊤ ⊤ 1 :=
  ⟨dvd_mul_right N r, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

theorem levelLE_top (hN : N ≠ 0) : LevelLE N (N * r) ⊤ ⊤ r :=
  ⟨dvd_mul_right N r, by rw [Nat.mul_div_cancel_left r (Nat.pos_of_ne_zero hN)],
    fun _ _ => Subgroup.mem_top _⟩

theorem levelLE_top_one' : LevelLE (N * r) (N * r * r) ⊤ ⊤ 1 :=
  ⟨dvd_mul_right _ r, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

theorem levelLE_top' (hNr : N * r ≠ 0) : LevelLE (N * r) (N * r * r) ⊤ ⊤ r :=
  ⟨dvd_mul_right _ r, by rw [Nat.mul_div_cancel_left r (Nat.pos_of_ne_zero hNr)],
    fun _ _ => Subgroup.mem_top _⟩

variable {N r}

theorem iDeg'_sub_apply {A : Type} [AddCommGroup A] (d : ℕ) [NeZero d]
    (hd : LevelLE N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) d) (hd' : LevelLE N (N * r) ⊤ ⊤ d)
    (φ : H1 N ⊤ A) (δ : ↥(GammaH (N * r) (CuspForm.AuxLevel.subgroup N r))) :
    iDeg' N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) d A hd φ (Additive.ofMul δ) =
      iDeg' N (N * r) ⊤ ⊤ d A hd' φ (Additive.ofMul (incl N r δ)) := by
  show φ (Additive.ofMul (iotaDeg N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) d hd δ)) =
    φ (Additive.ofMul (iotaDeg N (N * r) ⊤ ⊤ d hd' (incl N r δ)))
  congr 2

theorem pow_sub_one_mem (hr : r.Prime) (γ : ↥(GammaH (N * r) ⊤)) :
    ((γ ^ (r - 1) : ↥(GammaH (N * r) ⊤)) : SL(2, ℤ)) ∈
      GammaH (N * r) (CuspForm.AuxLevel.subgroup N r) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨h0, -⟩ := mem_GammaH_iff.mp γ.2
  have hpow : ((γ ^ (r - 1) : ↥(GammaH (N * r) ⊤)) : SL(2, ℤ)) = (γ : SL(2, ℤ)) ^ (r - 1) := rfl
  rw [hpow, mem_GammaH_iff]
  refine ⟨Subgroup.pow_mem _ h0 _, ?_⟩
  have h1 : (⟨(γ : SL(2, ℤ)) ^ (r - 1), Subgroup.pow_mem _ h0 _⟩ : Gamma0 (N * r)) =
      (⟨(γ : SL(2, ℤ)), h0⟩ : Gamma0 (N * r)) ^ (r - 1) := rfl
  rw [h1, map_pow]
  show ZMod.unitsMap (dvd_mul_left r N) (gamma0Units (N * r) ⟨(γ : SL(2, ℤ)), h0⟩ ^ (r - 1)) = 1
  rw [map_pow, ZMod.units_pow_card_sub_one_eq_one]

theorem eq_zero_of_comp_incl_eq_zero {A : Type} [AddCommGroup A] (hr : r.Prime)
    (hA : ∀ a : A, (r - 1) • a = 0 → a = 0) (x : H1 (N * r) ⊤ A)
    (hx : ∀ δ : ↥(GammaH (N * r) (CuspForm.AuxLevel.subgroup N r)), x (Additive.ofMul (incl N r δ)) = 0) :
    x = 0 := by
  apply AddMonoidHom.ext
  intro γ'
  set γ := Additive.toMul γ' with hγ
  have hγ' : γ' = Additive.ofMul γ := rfl

  let δ : ↥(GammaH (N * r) (CuspForm.AuxLevel.subgroup N r)) :=
    ⟨((γ ^ (r - 1) : ↥(GammaH (N * r) ⊤)) : SL(2, ℤ)), pow_sub_one_mem hr γ⟩
  have hδ : incl N r δ = γ ^ (r - 1) := Subtype.ext rfl
  have h0 : x (Additive.ofMul (γ ^ (r - 1))) = 0 := by rw [← hδ]; exact hx δ
  rw [ofMul_pow, map_nsmul] at h0
  rw [hγ', AddMonoidHom.zero_apply]
  exact hA _ h0

end IharaAux
p2m_reactivate "P2MW.S_CuspForm_AuxLevel_isEis_of_iDeg_one_add_iDeg_eq_zero.IharaAux"

open CohCarrier IharaAux in
theorem solution
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N r : ℕ) [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)
    (h₁ : CohCarrier.LevelLE N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1)
    (hr' : CohCarrier.LevelLE N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) r)
    (hA : ∀ a : A, (r - 1) • a = 0 → a = 0)
    (hℓ : ℓ₀.Prime) (hℓNr : ¬ ℓ₀ ∣ N * r)
    (g h : CohCarrier.H1 N ⊤ A)
    (hgh : CohCarrier.iDeg' N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1 A h₁ g +
      CohCarrier.iDeg' N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) r A hr' h = 0) :
    CohCarrier.IsEis R A N ⊤ ℓ₀ g ∧ CohCarrier.IsEis R A N ⊤ ℓ₀ h := by

  have hN : N ≠ 0 := fun h0 => hrN (h0 ▸ dvd_zero r)
  have hNr : N * r ≠ 0 := mul_ne_zero hN (NeZero.ne r)

  have h₁T := levelLE_top_one N r
  have hrT := levelLE_top N r hN
  have h₁T' := levelLE_top_one' N r
  have hrT' := levelLE_top' N r hNr

  set x : H1 (N * r) ⊤ A := iDeg' N (N * r) ⊤ ⊤ 1 A h₁T g + iDeg' N (N * r) ⊤ ⊤ r A hrT h with hxdef
  have hx : x = 0 := by
    apply eq_zero_of_comp_incl_eq_zero hr hA
    intro δ
    have := congrArg (fun F : H1 (N * r) (CuspForm.AuxLevel.subgroup N r) A => F (Additive.ofMul δ)) hgh
    simp only [AddMonoidHom.add_apply, AddMonoidHom.zero_apply] at this
    rw [iDeg'_sub_apply 1 h₁ h₁T g δ, iDeg'_sub_apply r hr' hrT h δ] at this
    rw [hxdef, AddMonoidHom.add_apply]
    exact this

  exact (CohCarrier.isEis_kernel_pair_of_prime R A ℓ₀ N r h₁T hrT h₁T' hrT' hr hrN hℓ hℓNr).1 g h
    (hxdef ▸ hx)

end S_CuspForm_AuxLevel_isEis_of_iDeg_one_add_iDeg_eq_zero
end P2MW
export P2MW.S_CuspForm_AuxLevel_isEis_of_iDeg_one_add_iDeg_eq_zero (solution)
