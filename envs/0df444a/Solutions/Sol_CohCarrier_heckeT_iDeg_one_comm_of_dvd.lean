-- Prove2me | solution 1 for CohCarrier.heckeT_iDeg_one_comm_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/263baeab-c89a-5ae1-bb24-9070bc0fc840

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_iDeg_one_comm_of_dvd

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
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_one_comm_of_dvd.IharaMintIdx"
end IdxBlock
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_one_comm_of_dvd.IharaMintIdx"

namespace IharaMintR2

open CohCarrier CongruenceSubgroup IharaMintUq
open scoped MatrixGroups

variable {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable [NeZero (N * q)]
variable (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)

omit [NeZero N] [NeZero q] [NeZero (N * q)] in

theorem iDeg_one_apply_ofMul (φ : H1 N ⊤ A) (z : ↥(GammaH (N * q) ⊤)) :
    iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ (Additive.ofMul z)
      = φ (Additive.ofMul (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ z)) := rfl

omit [NeZero N] [NeZero q] [NeZero (N * q)] in

theorem coe_iotaDeg_one_impl (γ : ↥(GammaH (N * q) ⊤)) :
    ((iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ : ↥(GammaH N ⊤)) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [iotaDeg, conjLowerMat, Matrix.of_apply, Fin.isValue]

omit [NeZero N] [NeZero q] [NeZero (N * q)] in

theorem iotaDeg_one_conjL_eq (s : ↥(GammaHUpper (N * q) ⊤ q)) :
    ((iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (conjL (N * q) ⊤ q s) : ↥(GammaH N ⊤)) : SL(2, ℤ))
      = conjUpperMat q (s : SL(2, ℤ)) (dvd_of_mem_GammaHUpper (N * q) ⊤ q s) := by
  rw [coe_iotaDeg_one_impl h₁]
  rfl

omit [NeZero N] [NeZero q] [NeZero (N * q)] in
theorem iotaDeg_one_mem_GammaHUpper_iff (z : ↥(GammaH (N * q) ⊤)) :
    iotaDeg N (N * q) ⊤ ⊤ 1 h₁ z ∈ GammaHUpper N ⊤ q ↔ z ∈ GammaHUpper (N * q) ⊤ q := by
  simp only [GammaHUpper, Subgroup.mem_subgroupOf, mem_Gamma0Upper, coe_iotaDeg_one_impl h₁]

omit [NeZero N] [NeZero q] [NeZero (N * q)] in

theorem conjL_iotaDeg_one_eq (s : ↥(GammaHUpper (N * q) ⊤ q))
    (hs : iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (s : ↥(GammaH (N * q) ⊤)) ∈ GammaHUpper N ⊤ q) :
    conjL N ⊤ q ⟨_, hs⟩ = iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (conjL (N * q) ⊤ q s) := by
  apply Subtype.ext
  rw [iotaDeg_one_conjL_eq h₁ s]
  show conjUpperMat q
      ((iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (s : ↥(GammaH (N * q) ⊤))) : SL(2, ℤ))
      (dvd_of_mem_GammaHUpper N ⊤ q ⟨_, hs⟩)
    = conjUpperMat q ((s : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ))
        (dvd_of_mem_GammaHUpper (N * q) ⊤ q s)
  congr 1
  exact coe_iotaDeg_one_impl h₁ _

omit [NeZero N] [NeZero q] [NeZero (N * q)] in

noncomputable def πCoset :
    Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q)) →
      Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q)) :=
  Quotient.map' (iotaDeg N (N * q) ⊤ ⊤ 1 h₁) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    rw [show (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ y) * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ x)⁻¹
      = iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (y * x⁻¹) from by rw [map_mul, map_inv]]
    exact (iotaDeg_one_mem_GammaHUpper_iff h₁ _).mpr h

omit [NeZero N] [NeZero q] [NeZero (N * q)] in
theorem πCoset_mk (γ' : ↥(GammaH (N * q) ⊤)) :
    πCoset h₁ (Quotient.mk'' γ') = Quotient.mk'' (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ') :=
  Quotient.map'_mk'' _ _ γ'

omit [NeZero N] [NeZero q] [NeZero (N * q)] in
theorem πCoset_injective : Function.Injective (πCoset h₁) := by
  intro a b hab
  induction a using Quotient.inductionOn' with
  | h x =>
    induction b using Quotient.inductionOn' with
    | h y =>
      rw [πCoset_mk, πCoset_mk] at hab
      have h := Quotient.exact' hab
      rw [QuotientGroup.rightRel_apply, ← map_inv, ← map_mul,
        iotaDeg_one_mem_GammaHUpper_iff h₁] at h
      exact Quotient.sound' (QuotientGroup.rightRel_apply.mpr h)

omit [NeZero N] [NeZero q] [NeZero (N * q)] in
theorem πCoset_mulRight (γ : ↥(GammaH (N * q) ⊤))
    (k : Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q))) :
    πCoset h₁ (mulRight (GammaHUpper (N * q) ⊤ q) γ k)
      = mulRight (GammaHUpper N ⊤ q) (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ) (πCoset h₁ k) := by
  induction k using Quotient.inductionOn' with
  | h x =>
    show πCoset h₁ (Quotient.mk'' (x * γ))
      = Quotient.mk'' (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ x * iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ)
    rw [πCoset_mk, map_mul]

omit [NeZero N] [NeZero q] [NeZero (N * q)] in

theorem rep_πCoset_mul_inv_mem (c' : Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q))) :
    rep (GammaHUpper N ⊤ q) (πCoset h₁ c')
        * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (rep (GammaHUpper (N * q) ⊤ q) c'))⁻¹
      ∈ GammaHUpper N ⊤ q := by
  have e : (Quotient.mk'' (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (rep (GammaHUpper (N * q) ⊤ q) c'))
        : Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q)))
      = Quotient.mk'' (rep (GammaHUpper N ⊤ q) (πCoset h₁ c')) := by
    rw [← πCoset_mk h₁]
    simp only [rep, Quotient.out_eq']
  have h := Quotient.exact' e
  rwa [QuotientGroup.rightRel_apply] at h

omit [NeZero N] [NeZero (N * q)] in

theorem sum_πCoset_eq (φ : H1 N ⊤ A) (γ' : ↥(GammaH (N * q) ⊤)) :
    ∑ c' : Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q)),
        φ (Additive.ofMul (conjL N ⊤ q
          (slip (GammaHUpper N ⊤ q) (πCoset h₁ c') (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ'))))
      = ∑ c' : Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q)),
        φ (Additive.ofMul (iotaDeg N (N * q) ⊤ ⊤ 1 h₁
          (conjL (N * q) ⊤ q (slip (GammaHUpper (N * q) ⊤ q) c' γ')))) := by
  have hT : ∀ c' : Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q)),
      slip (GammaHUpper N ⊤ q) (πCoset h₁ c') (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ')
        = (⟨_, rep_πCoset_mul_inv_mem h₁ c'⟩ : ↥(GammaHUpper N ⊤ q))
          * ⟨iotaDeg N (N * q) ⊤ ⊤ 1 h₁
              ((slip (GammaHUpper (N * q) ⊤ q) c' γ' : ↥(GammaHUpper (N * q) ⊤ q))
                : ↥(GammaH (N * q) ⊤)),
              (iotaDeg_one_mem_GammaHUpper_iff h₁ _).mpr (slip (GammaHUpper (N * q) ⊤ q) c' γ').2⟩
          * (⟨_, rep_πCoset_mul_inv_mem h₁ (mulRight (GammaHUpper (N * q) ⊤ q) γ' c')⟩
              : ↥(GammaHUpper N ⊤ q))⁻¹ := by
    intro c'
    apply Subtype.ext
    simp only [coe_slip, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [← mulRight_eq_cls_rep_mul (GammaHUpper N ⊤ q), ← πCoset_mulRight h₁,
      mulRight_eq_cls_rep_mul (GammaHUpper (N * q) ⊤ q) γ' c']
    group
  simp_rw [hT, map_mul, map_inv, ofMul_mul, ofMul_inv, map_add, map_neg]
  simp_rw [conjL_iotaDeg_one_eq h₁]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hperm : ∑ c' : Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q)),
        φ (Additive.ofMul (conjL N ⊤ q
          ⟨_, rep_πCoset_mul_inv_mem h₁ (mulRight (GammaHUpper (N * q) ⊤ q) γ' c')⟩))
      = ∑ c' : Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q)),
          φ (Additive.ofMul (conjL N ⊤ q ⟨_, rep_πCoset_mul_inv_mem h₁ c'⟩)) :=
    Equiv.sum_comp (mulRight (GammaHUpper (N * q) ⊤ q) γ')
      (fun c' => φ (Additive.ofMul (conjL N ⊤ q ⟨_, rep_πCoset_mul_inv_mem h₁ c'⟩)))
  rw [hperm]
  abel

omit [NeZero N] [NeZero q] in

theorem heckeT_apply_eq_sumEquiv_impl (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {V : Type} [AddCommGroup V] {ι : Type*} [Fintype ι]
    (e : ι ≃ Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)))
    (F : Additive ↥(GammaH M H) →+ V) (γ : ↥(GammaH M H)) :
    heckeT M H ℓ V F (Additive.ofMul γ)
      = ∑ i : ι, F (Additive.ofMul (conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ))) := by
  rw [heckeT_apply_eq_sum_impl M H ℓ F γ]
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

end IharaMintR2
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_one_comm_of_dvd.IharaMintIdx"

open CohCarrier IharaMintR2 in
theorem solution {N q : ℕ} [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hqN : q ∣ N) (φ : H1 N ⊤ A) :
    heckeT (N * q) ⊤ q A (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
      = iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨γ', rfl⟩ : ∃ γ', Additive.ofMul γ' = x := ⟨Additive.toMul x, rfl⟩
  have hcard : Fintype.card (Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q)))
      = Fintype.card (Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q))) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      IharaMintIdx.natCard_rightQuot (N * q) ⊤ q (dvd_mul_left q N),
      IharaMintIdx.natCard_rightQuot N ⊤ q hqN]
  have hbij : Function.Bijective (πCoset h₁) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨πCoset_injective h₁, hcard⟩
  rw [heckeT_apply_eq_sum_impl (N * q) ⊤ q _ γ']
  simp_rw [iDeg_one_apply_ofMul]
  rw [heckeT_apply_eq_sumEquiv_impl N ⊤ q (Equiv.ofBijective _ hbij) φ _]
  simp only [Equiv.ofBijective_apply]
  exact (sum_πCoset_eq h₁ φ γ').symm

end S_CohCarrier_heckeT_iDeg_one_comm_of_dvd
end P2MW
export P2MW.S_CohCarrier_heckeT_iDeg_one_comm_of_dvd (solution)
