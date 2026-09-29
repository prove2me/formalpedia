-- Prove2me | solution 1 for CohCarrier.heckeT_iDeg_interchange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ed4de9df-14a0-5f48-bda8-cea913118622

import Definitions.Def_CohCarrier_Level
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_iDeg_interchange

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
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_interchange.IharaMintIdx"
end IdxBlock
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_interchange.IharaMintIdx"

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
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_interchange.IharaMintIdx"

namespace IharaMintIdx

open CongruenceSubgroup
open scoped MatrixGroups

def gInf (b : ℤ) (M : ℕ) : SL(2, ℤ) :=
  ⟨!![1 + b * M, b; M, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem gInf_00 (b : ℤ) (M : ℕ) : (gInf b M) 0 0 = 1 + b * M := rfl
@[scoped simp] theorem gInf_01 (b : ℤ) (M : ℕ) : (gInf b M) 0 1 = b := rfl
@[scoped simp] theorem gInf_10 (b : ℤ) (M : ℕ) : (gInf b M) 1 0 = M := rfl
@[scoped simp] theorem gInf_11 (b : ℤ) (M : ℕ) : (gInf b M) 1 1 = 1 := rfl

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem gInf_mem (b : ℤ) : gInf b M ∈ CohCarrier.GammaH M H := by
  have h0 : gInf b M ∈ Gamma0 M := by
    rw [Gamma0_mem]; show (((M : ℕ) : ℤ) : ZMod M) = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : CohCarrier.gamma0Units M ⟨gInf b M, h0⟩ = 1 := by
    apply Units.ext; rw [CohCarrier.val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod M) = 1; exact Int.cast_one
  rw [e]; exact H.one_mem

def gElt (b : ℤ) : ↥(CohCarrier.GammaH M H) := ⟨gInf b M, gInf_mem M H b⟩

@[scoped simp] theorem gElt_coe (b : ℤ) :
    ((gElt M H b : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) = gInf b M := rfl

variable (ℓ : ℕ)

theorem natCard_rightQuot_good [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    Nat.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = ℓ + 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨u, v, huv⟩ : IsCoprime (ℓ : ℤ) (M : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)
  have Hl : ((ℓ : ℕ) : ZMod ℓ) = 0 := ZMod.natCast_self ℓ
  have Hc := congrArg (Int.cast : ℤ → ZMod ℓ) huv; push_cast at Hc
  have H0 : (1 : ZMod ℓ) + -(v : ZMod ℓ) * (M : ZMod ℓ) = 0 := by
    linear_combination -Hc + (u : ZMod ℓ) * Hl
  have H2 : (v : ZMod ℓ) * (M : ZMod ℓ) = 1 := by linear_combination Hc - (u : ZMod ℓ) * Hl
  have hNU : ∀ j : ZMod ℓ,
      (Quotient.mk'' (gElt M H (-v)) :
        Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) =
          Quotient.mk'' (uElt M H (j.val : ℤ)) → False := by
    intro j h
    rw [mk_eq_mk_iff, mul_inv_apply_01] at h
    simp only [uElt_coe, gElt_coe, uMat_00, uMat_01, gInf_00, gInf_01] at h
    push_cast at h; simp only [ZMod.natCast_zmod_val] at h
    have H3 : (v : ZMod ℓ) = 0 := by linear_combination h - j * H0
    exact zero_ne_one (by linear_combination H2 - (M : ZMod ℓ) * H3)
  have hUU : ∀ j j' : ZMod ℓ,
      (Quotient.mk'' (uElt M H (j.val : ℤ)) :
        Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) =
          Quotient.mk'' (uElt M H (j'.val : ℤ)) → j = j' := by
    intro j j' h
    rw [mk_eq_mk_iff, mul_inv_apply_01] at h
    simp only [uElt_coe, uMat_00, uMat_01] at h
    push_cast at h; simp only [ZMod.natCast_zmod_val] at h
    linear_combination -h
  let ψ : Option (ZMod ℓ) → Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ)) :=
    fun o => o.elim (Quotient.mk'' (gElt M H (-v))) fun j => Quotient.mk'' (uElt M H (j.val : ℤ))
  have hinj : Function.Injective ψ := by
    intro x y hxy
    cases x with
    | none => cases y with
      | none => rfl
      | some j => exact (hNU j hxy).elim
    | some j => cases y with
      | none => exact (hNU j hxy.symm).elim
      | some j' => exact congrArg some (hUU j j' hxy)
  have hsurj : Function.Surjective ψ := by
    intro q
    induction q using Quotient.inductionOn' with
    | h g =>
      by_cases ha : (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) = 0
      · refine ⟨none, ?_⟩
        show (Quotient.mk'' (gElt M H (-v)) :
            Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = Quotient.mk'' g
        rw [mk_eq_mk_iff, mul_inv_apply_01]
        simp only [gElt_coe, gInf_00, gInf_01]; push_cast
        linear_combination (v : ZMod ℓ) * ha + ((((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)) * H0
      · obtain ⟨j, hj⟩ : ∃ j : ZMod ℓ,
            (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) * j = (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) :=
          ⟨((((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ))⁻¹ * (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ), by
            rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩
        refine ⟨some j, ?_⟩
        show (Quotient.mk'' (uElt M H (j.val : ℤ)) :
            Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = Quotient.mk'' g
        rw [mk_eq_mk_iff, mul_inv_apply_01]
        simp only [uElt_coe, uMat_00, uMat_01]; push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination -hj
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_option, ZMod.card]

theorem card_rightQuot_good [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    Fintype.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = ℓ + 1 := by
  rw [← Nat.card_eq_fintype_card]; exact natCard_rightQuot_good M H ℓ hℓ hℓM

theorem card_rightQuot_bad [NeZero ℓ] (hℓM : ℓ ∣ M) :
    Fintype.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = ℓ := by
  rw [← Nat.card_eq_fintype_card]; exact natCard_rightQuot M H ℓ hℓM

end IharaMintIdx
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_interchange.IharaMintIdx"

namespace IharaMintR2

open CohCarrier CongruenceSubgroup IharaMintUq IharaMintIdx
open scoped MatrixGroups

variable {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [NeZero N] [NeZero q] in
@[scoped simp] theorem conjUpperMat_apply_00 (ℓ : ℕ) (X : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ X 0 1) :
    (conjUpperMat ℓ X h) 0 0 = X 0 0 := by simp [conjUpperMat]

omit [NeZero N] [NeZero q] in
@[scoped simp] theorem conjUpperMat_apply_01 (ℓ : ℕ) (X : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ X 0 1) :
    (conjUpperMat ℓ X h) 0 1 = X 0 1 / (ℓ : ℤ) := by simp [conjUpperMat]

omit [NeZero N] [NeZero q] in

theorem H1_apply_conj (φ : H1 N ⊤ A) (w x : ↥(GammaH N ⊤)) :
    φ (Additive.ofMul (w * x * w⁻¹)) = φ (Additive.ofMul x) := by
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg]; abel

omit [NeZero N] in

def wInftySL (u v : ℤ) (huv : u * q + v * N = 1) : SL(2, ℤ) :=
  ⟨!![u, -v; (N : ℤ), (q : ℤ)], by rw [Matrix.det_fin_two_of]; linarith [huv]⟩

omit [NeZero N] in

def wInfty (u v : ℤ) (huv : u * q + v * N = 1) : ↥(GammaH N ⊤) :=
  ⟨wInftySL u v huv, by
    rw [GammaH_top]
    exact CongruenceSubgroup.Gamma0_mem.mpr (by simp [wInftySL])⟩

set_option maxHeartbeats 1600000 in
omit [NeZero N] in

theorem conjUpperMat_gInf_conj_eq (u v : ℤ) (huv : u * q + v * N = 1)
    (X : SL(2, ℤ)) (hq : (q : ℤ) ∣ X 1 0)
    (h01 : (q : ℤ) ∣ (gInf (-v) N * X * (gInf (-v) N)⁻¹) 0 1) :
    conjUpperMat q (gInf (-v) N * X * (gInf (-v) N)⁻¹) h01
      = wInftySL u v huv * conjLowerMat q X hq * (wInftySL u v huv)⁻¹ := by
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have ⟨c', hc'⟩ := hq
  have huq : (1 : ℤ) + -v * N = u * q := by linarith [huv]
  have eTm : ((gInf (-v) N : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![1 + -v * (N : ℤ), -v; (N : ℤ), 1] := rfl
  have eTinvm : (((gInf (-v) N)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![1, v; -(N : ℤ), 1 + -v * (N : ℤ)] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, eTm, Matrix.adjugate_fin_two_of]; simp
  have eWm : ((wInftySL u v huv : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![u, -v; (N : ℤ), (q : ℤ)] := rfl
  have eWinvm : (((wInftySL u v huv)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(q : ℤ), v; -(N : ℤ), u] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, eWm, Matrix.adjugate_fin_two_of]; simp
  have eM : ∀ i j : Fin 2, (gInf (-v) N * X * (gInf (-v) N)⁻¹ : SL(2, ℤ)) i j
      = (!![1 + -v * (N : ℤ), -v; (N : ℤ), 1] * (X : Matrix (Fin 2) (Fin 2) ℤ)
          * !![1, v; -(N : ℤ), 1 + -v * (N : ℤ)]) i j := fun i j => by
    simp only [Matrix.SpecialLinearGroup.coe_mul, eTm, eTinvm]
  have eR : ∀ i j : Fin 2, (wInftySL u v huv * conjLowerMat q X hq * (wInftySL u v huv)⁻¹
        : SL(2, ℤ)) i j
      = (!![u, -v; (N : ℤ), (q : ℤ)] * !![X 0 0, X 0 1 * (q : ℤ); c', X 1 1]
          * !![(q : ℤ), v; -(N : ℤ), u]) i j := fun i j => by
    have eLowm : ((conjLowerMat q X hq : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = !![X 0 0, X 0 1 * (q : ℤ); c', X 1 1] := by
      show !![X 0 0, X 0 1 * (q : ℤ); X 1 0 / (q : ℤ), X 1 1] = _
      rw [hc', Int.mul_ediv_cancel_left _ hq0]
    simp only [Matrix.SpecialLinearGroup.coe_mul, eWm, eWinvm, eLowm]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j
  · show (conjUpperMat q _ h01 : SL(2, ℤ)) 0 0
      = (wInftySL u v huv * conjLowerMat q X hq * (wInftySL u v huv)⁻¹ : SL(2, ℤ)) 0 0
    rw [conjUpperMat_apply_00, eM 0 0, eR 0 0]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hc', huq]; ring
  · show (conjUpperMat q _ h01 : SL(2, ℤ)) 0 1
      = (wInftySL u v huv * conjLowerMat q X hq * (wInftySL u v huv)⁻¹ : SL(2, ℤ)) 0 1
    rw [conjUpperMat_apply_01, eM 0 1, eR 0 1]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hc', huq,
      show (u * (q : ℤ) * X 0 0 + -v * ((q : ℤ) * c')) * v
          + (u * (q : ℤ) * X 0 1 + -v * X 1 1) * (u * (q : ℤ))
        = (q : ℤ) * ((u * X 0 0 + -v * c') * v + (u * (X 0 1 * q) + -v * X 1 1) * u)
        from by ring,
      Int.mul_ediv_cancel_left _ hq0]
  · show (conjUpperMat q _ h01 : SL(2, ℤ)) 1 0
      = (wInftySL u v huv * conjLowerMat q X hq * (wInftySL u v huv)⁻¹ : SL(2, ℤ)) 1 0
    rw [conjUpperMat_apply_10, eM 1 0, eR 1 0]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hc']; ring
  · show (conjUpperMat q _ h01 : SL(2, ℤ)) 1 1
      = (wInftySL u v huv * conjLowerMat q X hq * (wInftySL u v huv)⁻¹ : SL(2, ℤ)) 1 1
    rw [conjUpperMat_apply_11, eM 1 1, eR 1 1]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hc', huq]; ring

variable [NeZero (N * q)]
variable (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)

omit [NeZero N] [NeZero (N * q)] in

theorem conjL_conj_gElt_eq_wInfty_conj_iotaDeg
    (u v : ℤ) (huv : u * q + v * N = 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (γ : ↥(GammaH (N * q) ⊤))
    (hmem : gElt N ⊤ (-v) * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ) * (gElt N ⊤ (-v))⁻¹
        ∈ GammaHUpper N ⊤ q) :
    conjL N ⊤ q ⟨_, hmem⟩
      = wInfty u v huv * iotaDeg N (N * q) ⊤ ⊤ q hq γ * (wInfty u v huv)⁻¹ := by
  apply Subtype.ext
  have hcoe : ((gElt N ⊤ (-v) * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ) * (gElt N ⊤ (-v))⁻¹
      : ↥(GammaH N ⊤)) : SL(2, ℤ))
      = gInf (-v) N * (γ : SL(2, ℤ)) * (gInf (-v) N)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, gElt_coe,
      coe_iotaDeg_one_impl h₁ γ]
  show conjUpperMat q
      ((gElt N ⊤ (-v) * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ) * (gElt N ⊤ (-v))⁻¹
        : ↥(GammaH N ⊤)) : SL(2, ℤ))
      (dvd_of_mem_GammaHUpper N ⊤ q ⟨_, hmem⟩)
    = wInftySL u v huv * conjLowerMat q (γ : SL(2, ℤ)) (hq.dvd_entry γ) * (wInftySL u v huv)⁻¹
  rw [← conjUpperMat_gInf_conj_eq u v huv (γ : SL(2, ℤ)) (hq.dvd_entry γ)
    (hcoe ▸ dvd_of_mem_GammaHUpper N ⊤ q ⟨_, hmem⟩)]
  congr 1

variable (v : ℤ) (hqp : q.Prime)

omit [NeZero N] [NeZero q] [NeZero (N * q)] in
theorem gElt_conj_iotaDeg_mem_GammaHUpper
    (H0 : (1 : ZMod q) + -(v : ZMod q) * (N : ZMod q) = 0) (γ : ↥(GammaH (N * q) ⊤)) :
    gElt N ⊤ (-v) * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ) * (gElt N ⊤ (-v))⁻¹
      ∈ GammaHUpper N ⊤ q := by
  rw [GammaHUpper, Subgroup.mem_subgroupOf, mem_Gamma0Upper, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, gElt_coe, coe_iotaDeg_one_impl h₁]
  have hc : ((γ : SL(2, ℤ)) 1 0 : ZMod q) = 0 := by
    have : (N * q : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        (CongruenceSubgroup.Gamma0_mem.mp (GammaH_top (M := N * q) ▸ γ.2))
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (dvd_trans (by exact_mod_cast dvd_mul_left q N) this)
  have eTm : (gInf (-v) N : SL(2, ℤ))
      = (!![1 + -v * (N : ℤ), -v; (N : ℤ), 1] : Matrix _ _ _) := rfl
  have eTinvm : ((gInf (-v) N)⁻¹ : SL(2, ℤ))
      = (!![1, v; -(N : ℤ), 1 + -v * (N : ℤ)] : Matrix _ _ _) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, eTm, Matrix.adjugate_fin_two_of]; ring_nf
  rw [show (gInf (-v) N * (γ : SL(2, ℤ)) * (gInf (-v) N)⁻¹ : SL(2, ℤ)) 0 1
    = ((1 + -v * (N : ℤ)) * (γ : SL(2, ℤ)) 0 0 + -v * (γ : SL(2, ℤ)) 1 0) * v
      + ((1 + -v * (N : ℤ)) * (γ : SL(2, ℤ)) 0 1 + -v * (γ : SL(2, ℤ)) 1 1)
        * (1 + -v * (N : ℤ)) from by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, eTm, eTinvm,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]]
  push_cast; rw [hc, H0]; ring

omit [NeZero N] [NeZero q] [NeZero (N * q)] in
include hqp in
theorem gElt_notMem_range_πCoset (H0 : (1 : ZMod q) + -(v : ZMod q) * (N : ZMod q) = 0)
    (H2 : (v : ZMod q) * (N : ZMod q) = 1) :
    (Quotient.mk'' (gElt N ⊤ (-v)) :
        Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q))) ∉ Set.range (πCoset h₁) := by
  haveI : Fact q.Prime := ⟨hqp⟩
  rintro ⟨k, hk⟩
  induction k using Quotient.inductionOn' with
  | h γ' =>
    rw [πCoset_mk] at hk
    have hmem := Quotient.exact' hk
    rw [QuotientGroup.rightRel_apply, GammaHUpper, Subgroup.mem_subgroupOf, mem_Gamma0Upper,
      Subgroup.coe_mul, Subgroup.coe_inv, gElt_coe, coe_iotaDeg_one_impl h₁] at hmem
    have hc : ((γ' : SL(2, ℤ)) 1 0 : ZMod q) = 0 := by
      have : (N * q : ℤ) ∣ (γ' : SL(2, ℤ)) 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
          (CongruenceSubgroup.Gamma0_mem.mp (GammaH_top (M := N * q) ▸ γ'.2))
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (dvd_trans (by exact_mod_cast dvd_mul_left q N) this)
    have hdet : ((γ' : SL(2, ℤ)) 0 0 * (γ' : SL(2, ℤ)) 1 1
        - (γ' : SL(2, ℤ)) 0 1 * (γ' : SL(2, ℤ)) 1 0 : ZMod q) = 1 := by
      have e := (γ' : SL(2, ℤ)).2; rw [Matrix.det_fin_two] at e
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod q) e
    have h01 : (gInf (-v) N * (γ' : SL(2, ℤ))⁻¹ : SL(2, ℤ)) 0 1 =
        -((1 + -v * (N : ℤ)) * (γ' : SL(2, ℤ)) 0 1) + -v * (γ' : SL(2, ℤ)) 0 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      show (gInf (-v) N : SL(2, ℤ)) 0 0 * -(γ' : SL(2, ℤ)) 0 1
        + (gInf (-v) N : SL(2, ℤ)) 0 1 * (γ' : SL(2, ℤ)) 0 0 = _
      simp only [gInf_00, gInf_01]; ring
    rw [h01] at hmem; push_cast at hmem
    have ha : ((γ' : SL(2, ℤ)) 0 0 : ZMod q) = 0 := by
      have hva : (v : ZMod q) * ((γ' : SL(2, ℤ)) 0 0 : ZMod q) = 0 := by
        linear_combination -hmem - ((γ' : SL(2, ℤ)) 0 1 : ZMod q) * H0
      linear_combination (N : ZMod q) * hva - ((γ' : SL(2, ℤ)) 0 0 : ZMod q) * H2
    rw [ha, zero_mul, hc, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet

omit [NeZero N] [NeZero (N * q)] in
include hqp in
theorem mem_range_πCoset_of_ne (hqN : ¬ q ∣ N)
    (H0 : (1 : ZMod q) + -(v : ZMod q) * (N : ZMod q) = 0)
    (H2 : (v : ZMod q) * (N : ZMod q) = 1)
    (r : Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q)))
    (hr : r ≠ Quotient.mk'' (gElt N ⊤ (-v))) : r ∈ Set.range (πCoset h₁) := by
  classical
  haveI : Fact q.Prime := ⟨hqp⟩
  have hcard_dom :
      Fintype.card (Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) ⊤ q))) = q :=
    card_rightQuot_bad (N * q) ⊤ q (dvd_mul_left q N)
  have hcard_cod :
      Fintype.card (Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q))) = q + 1 :=
    card_rightQuot_good N ⊤ q hqp hqN
  have himg : (Finset.univ.image (πCoset h₁)).card = q := by
    rw [Finset.card_image_of_injective _ (πCoset_injective h₁), Finset.card_univ, hcard_dom]
  have hnot : Quotient.mk'' (gElt N ⊤ (-v)) ∉ Finset.univ.image (πCoset h₁) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact fun ⟨k, hk⟩ => gElt_notMem_range_πCoset h₁ v hqp H0 H2 ⟨k, hk⟩
  have heq : insert (Quotient.mk'' (gElt N ⊤ (-v))) (Finset.univ.image (πCoset h₁))
      = Finset.univ :=
    (Finset.card_eq_iff_eq_univ _).mp (by
      rw [Finset.card_insert_of_notMem hnot, himg, hcard_cod])
  have hrm : r ∈ insert (Quotient.mk'' (gElt N ⊤ (-v))) (Finset.univ.image (πCoset h₁)) :=
    heq ▸ Finset.mem_univ r
  rcases Finset.mem_insert.mp hrm with h | h
  · exact (hr h).elim
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h; exact ⟨k, hk⟩

variable (u : ℤ) (huv : u * q + v * N = 1)
variable (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)

omit [NeZero N] [NeZero (N * q)] in
include hq u huv in
theorem phi_conjL_slip_gElt_eq
    (H0 : (1 : ZMod q) + -(v : ZMod q) * (N : ZMod q) = 0)
    (φ : H1 N ⊤ A) (γ' : ↥(GammaH (N * q) ⊤)) :
    φ (Additive.ofMul (conjL N ⊤ q (slip (GammaHUpper N ⊤ q)
        (Quotient.mk'' (gElt N ⊤ (-v))) (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ'))))
      = φ (Additive.ofMul (iotaDeg N (N * q) ⊤ ⊤ q hq γ')) := by
  have hmem : gElt N ⊤ (-v) * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ') * (gElt N ⊤ (-v))⁻¹
      ∈ GammaHUpper N ⊤ q := gElt_conj_iotaDeg_mem_GammaHUpper h₁ v H0 γ'
  have hstab : cls (GammaHUpper N ⊤ q)
      (rep (GammaHUpper N ⊤ q) (Quotient.mk'' (gElt N ⊤ (-v)))
        * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ')) = Quotient.mk'' (gElt N ⊤ (-v)) := by
    rw [show (Quotient.mk'' (gElt N ⊤ (-v)) :
        Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q)))
      = cls (GammaHUpper N ⊤ q) (gElt N ⊤ (-v)) from rfl,
      cls_rep_mul (GammaHUpper N ⊤ q) (gElt N ⊤ (-v)) (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ')]
    refine Quotient.sound' (QuotientGroup.rightRel_apply.mpr ?_)
    rw [show gElt N ⊤ (-v) * (gElt N ⊤ (-v) * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ'))⁻¹
      = (gElt N ⊤ (-v) * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ') * (gElt N ⊤ (-v))⁻¹)⁻¹ from by group]
    exact (GammaHUpper N ⊤ q).inv_mem hmem
  have hsInf : rep (GammaHUpper N ⊤ q) (Quotient.mk'' (gElt N ⊤ (-v))) * (gElt N ⊤ (-v))⁻¹
      ∈ GammaHUpper N ⊤ q := by
    have h := Quotient.exact' (Quotient.out_eq' (Quotient.mk'' (gElt N ⊤ (-v)) :
      Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q))))
    rw [QuotientGroup.rightRel_apply] at h
    have h__af := (GammaHUpper N ⊤ q).inv_mem h
    simp at h__af
    exact h__af
  have hslip : slip (GammaHUpper N ⊤ q) (Quotient.mk'' (gElt N ⊤ (-v)))
        (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ')
      = (⟨_, hsInf⟩ : ↥(GammaHUpper N ⊤ q)) * ⟨_, hmem⟩ * (⟨_, hsInf⟩)⁻¹ := by
    apply Subtype.ext
    show rep (GammaHUpper N ⊤ q) (Quotient.mk'' (gElt N ⊤ (-v)))
        * (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ')
        * (rep (GammaHUpper N ⊤ q) (cls (GammaHUpper N ⊤ q) _))⁻¹ = _
    rw [hstab]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [hslip,
    show conjL N ⊤ q ((⟨_, hsInf⟩ : ↥(GammaHUpper N ⊤ q)) * ⟨_, hmem⟩ * (⟨_, hsInf⟩)⁻¹)
      = conjL N ⊤ q ⟨_, hsInf⟩ * conjL N ⊤ q ⟨_, hmem⟩ * (conjL N ⊤ q ⟨_, hsInf⟩)⁻¹ from by
      simp only [map_mul, map_inv],
    H1_apply_conj, conjL_conj_gElt_eq_wInfty_conj_iotaDeg h₁ u v huv hq γ' hmem, H1_apply_conj]

end IharaMintR2
p2m_reactivate "P2MW.S_CohCarrier_heckeT_iDeg_interchange.IharaMintIdx P2MW.S_CohCarrier_heckeT_iDeg_interchange.IharaMintR2"

open CohCarrier IharaMintR2 IharaMintIdx IharaMintUq

theorem solution {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (hqp : q.Prime) (hqN : ¬ q ∣ N)
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (φ : H1 N ⊤ A) :
    heckeT (N * q) ⊤ q A (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
      = iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ)
          - iDeg' N (N * q) ⊤ ⊤ q A hq φ := by
  classical
  haveI : Fact q.Prime := ⟨hqp⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * q + v * N = 1 := by
    have hcop : Nat.Coprime q N := (hqp.coprime_iff_not_dvd).mpr hqN
    obtain ⟨u, v, h⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨u, v, by linarith [h]⟩
  have H2 : (v : ZMod q) * (N : ZMod q) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q)) huv
    push_cast at h; rw [ZMod.natCast_self, mul_zero, zero_add] at h; exact h
  have H0 : (1 : ZMod q) + -(v : ZMod q) * (N : ZMod q) = 0 := by linear_combination -H2
  apply AddMonoidHom.ext; intro x
  obtain ⟨γ', rfl⟩ : ∃ γ', Additive.ofMul γ' = x := ⟨Additive.toMul x, rfl⟩
  rw [AddMonoidHom.sub_apply]
  rw [heckeT_apply_eq_sum_impl (N * q) ⊤ q (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ) γ']
  simp_rw [iDeg_one_apply_ofMul h₁]
  rw [heckeT_apply_eq_sum_impl N ⊤ q φ (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ γ')]
  have hnot : Quotient.mk'' (gElt N ⊤ (-v)) ∉ Finset.univ.image (πCoset h₁) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact fun ⟨k, hk⟩ => gElt_notMem_range_πCoset h₁ v hqp H0 H2 ⟨k, hk⟩
  have heq_univ : insert (Quotient.mk'' (gElt N ⊤ (-v))) (Finset.univ.image (πCoset h₁))
      = (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q)))) := by
    refine Finset.eq_univ_iff_forall.mpr fun r => ?_
    rcases eq_or_ne r (Quotient.mk'' (gElt N ⊤ (-v))) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · obtain ⟨k, hk⟩ := mem_range_πCoset_of_ne h₁ v hqp hqN H0 H2 r h
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  rw [show (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (GammaHUpper N ⊤ q))))
      = insert (Quotient.mk'' (gElt N ⊤ (-v))) (Finset.univ.image (πCoset h₁))
      from heq_univ.symm,
    Finset.sum_insert hnot,
    Finset.sum_image (fun a _ b _ hab => πCoset_injective h₁ hab)]
  rw [sum_πCoset_eq h₁ φ γ']
  rw [phi_conjL_slip_gElt_eq h₁ v u huv hq H0 φ γ']
  show _ = _ + _ - φ (Additive.ofMul (iotaDeg N (N * q) ⊤ ⊤ q hq γ'))
  abel

#print axioms solution

end S_CohCarrier_heckeT_iDeg_interchange
end P2MW
export P2MW.S_CohCarrier_heckeT_iDeg_interchange (solution)
