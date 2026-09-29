-- Prove2me | solution 1 for CohCarrier.heckeT_comp_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b5e23dc2-6500-5209-a6b0-8822af9f4e81

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_comp_coeff

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
theorem solution (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type}
    [AddCommGroup A] [AddCommGroup B] (ℓ : ℕ) [NeZero ℓ] (g : A →+ B) (φ : H1 M H A) :
    heckeT M H ℓ B (g.comp φ) = g.comp (heckeT M H ℓ A φ) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨γ, rfl⟩ : ∃ γ, Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
  show heckeT M H ℓ B (g.comp φ) (Additive.ofMul γ) = g (heckeT M H ℓ A φ (Additive.ofMul γ))
  rw [heckeT_apply_eq_sum_impl M H ℓ (g.comp φ) γ, heckeT_apply_eq_sum_impl M H ℓ φ γ, map_sum]
  rfl

end S_CohCarrier_heckeT_comp_coeff
end P2MW
export P2MW.S_CohCarrier_heckeT_comp_coeff (solution)
