-- Prove2me | solution 1 for CohCarrier.heckeT_iDeg_q_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c1d45236-8970-5041-923d-d23584b7479a

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_iDeg_q_eq_smul

set_option autoImplicit false

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace IharaMintUq

variable {Γ : Type} [Group Γ] (S₂ : Subgroup Γ)

noncomputable def rep (q : Quotient (QuotientGroup.rightRel S₂)) : Γ := q.out

abbrev cls (g : Γ) : Quotient (QuotientGroup.rightRel S₂) := Quotient.mk _ g

noncomputable def slip (q : Quotient (QuotientGroup.rightRel S₂)) (γ : Γ) : S₂ :=
  ⟨rep S₂ q * γ * (rep S₂ (cls S₂ (rep S₂ q * γ)))⁻¹, by
    have h : QuotientGroup.rightRel S₂ (rep S₂ (cls S₂ (rep S₂ q * γ))) (rep S₂ q * γ) :=
      Quotient.exact' (by simp [rep, cls])
    rw [QuotientGroup.rightRel_apply] at h
    simpa [mul_assoc] using h⟩

theorem coe_slip (q : Quotient (QuotientGroup.rightRel S₂)) (γ : Γ) :
    (slip S₂ q γ : Γ) = rep S₂ q * γ * (rep S₂ (cls S₂ (rep S₂ q * γ)))⁻¹ := rfl

theorem cls_rep_mul (x δ : Γ) : cls S₂ (rep S₂ (cls S₂ x) * δ) = cls S₂ (x * δ) := by
  apply Quotient.sound'
  have h : QuotientGroup.rightRel S₂ (rep S₂ (cls S₂ x)) x := Quotient.exact' (by simp [rep, cls])
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa [mul_assoc] using h

noncomputable def mulRight (γ : Γ) : Quotient (QuotientGroup.rightRel S₂) ≃ Quotient (QuotientGroup.rightRel S₂) where
  toFun := Quotient.map' (· * γ) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢; simpa [mul_assoc] using h
  invFun := Quotient.map' (· * γ⁻¹) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢; simpa [mul_assoc] using h
  left_inv q := Quotient.inductionOn' q fun x => by simp [Quotient.map'_mk'', mul_assoc]
  right_inv q := Quotient.inductionOn' q fun x => by simp [Quotient.map'_mk'', mul_assoc]

theorem mulRight_eq_cls_rep_mul (γ : Γ) (x : Quotient (QuotientGroup.rightRel S₂)) :
    mulRight S₂ γ x = cls S₂ (rep S₂ x * γ) := by
  induction x using Quotient.inductionOn' with
  | h y =>
    show cls S₂ (y * γ) = cls S₂ (rep S₂ (cls S₂ y) * γ)
    exact (cls_rep_mul S₂ y γ).symm

def toRight : Γ ⧸ S₂ ≃ Quotient (QuotientGroup.rightRel S₂) :=
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel S₂).symm

noncomputable def secL (p : Γ ⧸ S₂) : Γ := (rep S₂ (toRight S₂ p))⁻¹

theorem secL_spec (p : Γ ⧸ S₂) : (QuotientGroup.mk (secL S₂ p) : Γ ⧸ S₂) = p := by
  induction p using QuotientGroup.induction_on with
  | H g =>
    show (QuotientGroup.mk ((rep S₂ (cls S₂ g⁻¹))⁻¹) : Γ ⧸ S₂) = QuotientGroup.mk g
    have h : QuotientGroup.rightRel S₂ (rep S₂ (cls S₂ g⁻¹)) g⁻¹ := Quotient.exact' (by simp [rep, cls])
    rw [QuotientGroup.rightRel_apply] at h
    rw [QuotientGroup.eq, inv_inv]
    simpa [mul_assoc] using S₂.inv_mem h

theorem toRight_inv_smul (γ : Γ) (p : Γ ⧸ S₂) :
    toRight S₂ (γ⁻¹ • p) = cls S₂ (rep S₂ (toRight S₂ p) * γ) := by
  induction p using QuotientGroup.induction_on with
  | H g =>
    show cls S₂ (γ⁻¹ * g)⁻¹ = cls S₂ (rep S₂ (cls S₂ g⁻¹) * γ)
    rw [cls_rep_mul, mul_inv_rev, inv_inv]

noncomputable def transL : S₂.LeftTransversal :=
  ⟨Set.range (secL S₂), Subgroup.isComplement_range_left (secL_spec S₂)⟩

theorem transL_apply (p : Γ ⧸ S₂) : ((transL S₂).2.leftQuotientEquiv p : Γ) = secL S₂ p :=
  Subgroup.IsComplement.leftQuotientEquiv_apply (secL_spec S₂) p

theorem toAdditiveLeft_transfer_apply [S₂.FiniteIndex] {V : Type} [AddCommGroup V]
    (ψ : ↥S₂ →* Multiplicative V) (g : Γ) :
    MonoidHom.toAdditiveLeft (MonoidHom.transfer ψ) (Additive.ofMul g) =
      ∑ q : Quotient (QuotientGroup.rightRel S₂), (ψ (slip S₂ q g)).toAdd := by
  have hdiff : Subgroup.leftTransversals.diff ψ (transL S₂) (g • transL S₂) =
      ∏ p : Γ ⧸ S₂, ψ (slip S₂ (toRight S₂ p) g) := by
    unfold Subgroup.leftTransversals.diff
    refine Fintype.prod_congr _ _ fun p => congrArg ψ (Subtype.ext ?_)
    show ((transL S₂).2.leftQuotientEquiv p : Γ)⁻¹ * ((g • transL S₂).2.leftQuotientEquiv p : Γ) = _
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, transL_apply, transL_apply, smul_eq_mul, coe_slip]
    simp only [secL, inv_inv]
    rw [toRight_inv_smul, mul_assoc]
  show ((MonoidHom.transfer ψ) g).toAdd = _
  rw [MonoidHom.transfer_def ψ (transL S₂) g, hdiff, toAdd_prod]
  exact Fintype.sum_equiv (toRight S₂) _ _ fun p => rfl

end IharaMintUq

open IharaMintUq CohCarrier in

theorem heckeT_apply_eq_sum_impl (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {V : Type} [AddCommGroup V] (F : Additive ↥(GammaH M H) →+ V) (γ : ↥(GammaH M H)) :
    heckeT M H ℓ V F (Additive.ofMul γ) =
      ∑ q : Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)),
        F (Additive.ofMul (conjL M H ℓ (slip (GammaHUpper M H ℓ) q γ))) :=
  toAdditiveLeft_transfer_apply (GammaHUpper M H ℓ)
    ((AddMonoidHom.toMultiplicativeRight F).comp (conjL M H ℓ)) γ

open IharaMintUq CohCarrier in
theorem heckeT_card_smul_impl (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] {V : Type} [AddCommGroup V]
    (F ψ : Additive ↥(GammaH M H) →+ V)
    (hF : ∀ s : ↥(GammaHUpper M H ℓ),
      F (Additive.ofMul (conjL M H ℓ s)) = ψ (Additive.ofMul (s : ↥(GammaH M H))))
    (γ : ↥(GammaH M H)) :
    heckeT M H ℓ V F (Additive.ofMul γ)
      = Fintype.card (Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ))) •
          ψ (Additive.ofMul γ) := by
  rw [heckeT_apply_eq_sum_impl M H ℓ F γ]
  simp_rw [hF]
  have hval : ∀ x : Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)),
      ((slip (GammaHUpper M H ℓ) x γ : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H))
        = rep (GammaHUpper M H ℓ) x * γ *
            (rep (GammaHUpper M H ℓ)
              (cls (GammaHUpper M H ℓ) (rep (GammaHUpper M H ℓ) x * γ)))⁻¹ :=
    fun x => rfl
  simp_rw [hval, ofMul_mul, ofMul_inv, map_add, map_neg]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Finset.sum_neg_distrib]
  have hperm : ∑ x : Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)),
        ψ (Additive.ofMul (rep (GammaHUpper M H ℓ)
          (cls (GammaHUpper M H ℓ) (rep (GammaHUpper M H ℓ) x * γ))))
      = ∑ x : Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)),
          ψ (Additive.ofMul (rep (GammaHUpper M H ℓ) x)) := by
    simp_rw [← mulRight_eq_cls_rep_mul (GammaHUpper M H ℓ) γ]
    exact Equiv.sum_comp (mulRight (GammaHUpper M H ℓ) γ)
      (fun x => ψ (Additive.ofMul (rep (GammaHUpper M H ℓ) x)))
  rw [hperm]
  abel

section IdxBlock
open CongruenceSubgroup
open scoped MatrixGroups
namespace IharaMintIdx

theorem mul_inv_apply_01 (x y : SL(2, ℤ)) : (x * y⁻¹) 0 1 = -(x 0 0 * y 0 1) + x 0 1 * y 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def uMat (t : ℤ) : SL(2, ℤ) :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem uMat_00 (t : ℤ) : (uMat t) 0 0 = 1 := rfl
@[scoped simp] theorem uMat_01 (t : ℤ) : (uMat t) 0 1 = t := rfl

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

theorem uMat_mem (t : ℤ) : uMat t ∈ CohCarrier.GammaH M H := by
  have h0 : uMat t ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show ((0 : ℤ) : ZMod M) = 0
    exact Int.cast_zero
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : CohCarrier.gamma0Units M ⟨uMat t, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod M) = 1
    exact Int.cast_one
  rw [e]
  exact H.one_mem

def uElt (t : ℤ) : ↥(CohCarrier.GammaH M H) := ⟨uMat t, uMat_mem M H t⟩

@[scoped simp] theorem uElt_coe (t : ℤ) : ((uElt M H t : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) = uMat t := rfl

theorem mk_eq_mk_iff (x y : ↥(CohCarrier.GammaH M H)) :
    (Quotient.mk'' x : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = Quotient.mk'' y ↔
      ((((y : SL(2, ℤ)) * (x : SL(2, ℤ))⁻¹) 0 1 : ℤ) : ZMod ℓ) = 0 := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper, Subgroup.coe_mul,
    Subgroup.coe_inv]

theorem natCard_rightQuot [NeZero ℓ] (hℓM : ℓ ∣ M) :
    Nat.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = ℓ := by
  have hUU : ∀ j j' : ZMod ℓ,
      (Quotient.mk'' (uElt M H (j.val : ℤ)) : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) =
        Quotient.mk'' (uElt M H (j'.val : ℤ)) → j = j' := by
    intro j j' h
    rw [mk_eq_mk_iff, mul_inv_apply_01] at h
    simp only [uElt_coe, uMat_00, uMat_01] at h
    push_cast at h
    simp only [ZMod.natCast_zmod_val] at h
    linear_combination -h
  let ψ : ZMod ℓ → Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ)) :=
    fun j => Quotient.mk'' (uElt M H (j.val : ℤ))
  have hinj : Function.Injective ψ := fun j j' h => hUU j j' h
  have hsurj : Function.Surjective ψ := by
    intro q
    induction q using Quotient.inductionOn' with
    | h g =>
      have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
      rw [Matrix.det_fin_two] at hdet
      have hdet' := congrArg (Int.cast : ℤ → ZMod ℓ) hdet
      push_cast at hdet'
      have hg0 : ((g : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 M := (CohCarrier.mem_GammaH_iff.mp g.2).1
      have hc : ((((g : SL(2, ℤ)) 1 0 : ℤ)) : ZMod ℓ) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg0
        exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓM) hg0
      refine ⟨(((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) * (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ), ?_⟩
      show (Quotient.mk'' (uElt M H (((((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) *
          (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)).val : ℤ)) :
          Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = Quotient.mk'' g
      rw [mk_eq_mk_iff, mul_inv_apply_01]
      simp only [uElt_coe, uMat_00, uMat_01]
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination (-((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ)) * hdet'
        + (-(((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ) * ((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ))) * hc
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card, ZMod.card]

end IharaMintIdx
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_q_eq_smul.IharaMintIdx"
end IdxBlock
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_q_eq_smul.IharaMintIdx"

namespace IharaMintUq3

open CohCarrier CongruenceSubgroup IharaMintUq IharaMintIdx
open scoped MatrixGroups

variable {N q : ℕ} [NeZero q] {A : Type} [AddCommGroup A]

omit [NeZero q] in

theorem coe_iotaDeg_one_impl [NeZero (N * q)]
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (γ : ↥(GammaH (N * q) ⊤)) :
    ((iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ : ↥(GammaH N ⊤)) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [iotaDeg, conjLowerMat, Matrix.of_apply, Fin.isValue]

theorem coe_iotaDeg_q_conjL_impl [NeZero (N * q)]
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (s : ↥(GammaHUpper (N * q) ⊤ q)) :
    ((iotaDeg N (N * q) ⊤ ⊤ q hq (conjL (N * q) ⊤ q s) : ↥(GammaH N ⊤)) : SL(2, ℤ))
      = ((s : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) := by
  have hb : (q : ℤ) ∣ ((s : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1 :=
    dvd_of_mem_GammaHUpper (N * q) ⊤ q s
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have h01 : ((s : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1 / q * q
      = ((s : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1 := Int.ediv_mul_cancel hb
  have h10 : ((s : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 * q / q
      = ((s : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 := Int.mul_ediv_cancel _ hq0
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [iotaDeg, conjL, conjLowerMat, conjUpperMat, Matrix.of_apply, Fin.isValue, h01, h10]

theorem iotaDeg_q_conjL_eq_iotaDeg_one_impl [NeZero (N * q)]
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (s : ↥(GammaHUpper (N * q) ⊤ q)) :
    iotaDeg N (N * q) ⊤ ⊤ q hq (conjL (N * q) ⊤ q s)
      = iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (s : ↥(GammaH (N * q) ⊤)) :=
  Subtype.ext ((coe_iotaDeg_q_conjL_impl hq s).trans (coe_iotaDeg_one_impl h₁ _).symm)

theorem card_rightQuot_mul_impl [NeZero (N * q)] :
    Fintype.card (Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q))) = q := by
  rw [← Nat.card_eq_fintype_card]
  exact IharaMintIdx.natCard_rightQuot (N * q) ⊤ q (dvd_mul_left q N)

end IharaMintUq3
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_q_eq_smul.IharaMintIdx"

open CohCarrier IharaMintUq3 in
theorem solution {N q : ℕ} [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (φ : H1 N ⊤ A) :
    heckeT (N * q) ⊤ q A (iDeg' N (N * q) ⊤ ⊤ q A hq φ)
      = q • iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨γ, rfl⟩ : ∃ γ, Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
  have hF : ∀ s : ↥(GammaHUpper (N * q) ⊤ q),
      iDeg' N (N * q) ⊤ ⊤ q A hq φ (Additive.ofMul (conjL (N * q) ⊤ q s))
        = iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ (Additive.ofMul (s : ↥(GammaH (N * q) ⊤))) := by
    intro s
    show φ (Additive.ofMul (iotaDeg N (N * q) ⊤ ⊤ q hq (conjL (N * q) ⊤ q s)))
      = φ (Additive.ofMul (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (s : ↥(GammaH (N * q) ⊤))))
    rw [iotaDeg_q_conjL_eq_iotaDeg_one_impl h₁ hq s]
  rw [heckeT_card_smul_impl (N * q) ⊤ q _ _ hF γ, card_rightQuot_mul_impl]
  rfl

end S_CohCarrier_heckeT_iDeg_q_eq_smul
end P2MW
export P2MW.S_CohCarrier_heckeT_iDeg_q_eq_smul (solution)
