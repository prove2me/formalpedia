-- Prove2me | solution 1 for CohCarrier.iDegP_jDeg_eq_finsum_diamondL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c0fa749f-d0ab-5143-9690-746a303506e6

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_iDegP_jDeg_eq_finsum_diamondL

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace NormSol

open CohCarrier

variable {L : ℕ} [NeZero L] {H H' : Subgroup (ZMod L)ˣ} (h : LevelLE L L H' H 1)

theorem coe_iotaDeg_one (γ : ↥(GammaH L H)) :
    ((iotaDeg L L H' H 1 h γ : ↥(GammaH L H')) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  show (conjLowerMat 1 (γ : SL(2, ℤ)) (h.dvd_entry γ)) i j = (γ : SL(2, ℤ)) i j
  fin_cases i <;> fin_cases j <;> simp [conjLowerMat]

theorem mem_range_iff (x : ↥(GammaH L H')) :
    x ∈ (iotaDeg L L H' H 1 h).range ↔ (x : SL(2, ℤ)) ∈ GammaH L H := by
  constructor
  · rintro ⟨γ, rfl⟩
    rw [coe_iotaDeg_one]
    exact γ.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subtype.ext (coe_iotaDeg_one h ⟨x, hx⟩)⟩

def unitsChar (L : ℕ) (H' : Subgroup (ZMod L)ˣ) : ↥(GammaH L H') →* ↥H' :=
  ((gamma0Units L).comp (Subgroup.inclusion (GammaH_le_Gamma0 H'))).codRestrict H'
    (fun x => (mem_GammaH_iff.mp x.2).2)

theorem coe_unitsChar (x : ↥(GammaH L H')) :
    (unitsChar L H' x : (ZMod L)ˣ) = gamma0Units L ⟨x, GammaH_le_Gamma0 H' x.2⟩ := rfl

theorem mem_range_iff_unitsChar (x : ↥(GammaH L H')) :
    x ∈ (iotaDeg L L H' H 1 h).range ↔ unitsChar L H' x ∈ H.subgroupOf H' := by
  rw [mem_range_iff, mem_GammaH_iff, Subgroup.mem_subgroupOf, coe_unitsChar]
  exact ⟨fun ⟨_, hu⟩ => hu, fun hu => ⟨_, hu⟩⟩

scoped instance range_normal : ((iotaDeg L L H' H 1 h).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_range_iff_unitsChar] at hn ⊢
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  exact hn

theorem unitsChar_surjective : Function.Surjective (unitsChar L H') := by
  intro u
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective L (u : (ZMod L)ˣ)
  have hσH : (σ : SL(2, ℤ)) ∈ GammaH L H' := mem_GammaH_iff.mpr ⟨σ.2, by
    rw [Subtype.coe_eta, hσ]; exact u.2⟩
  refine ⟨⟨σ, hσH⟩, Subtype.ext ?_⟩
  rw [coe_unitsChar, ← hσ]

variable (𝒪 : Type) [CommRing 𝒪]

theorem diamondRaw_mul (σ τ : ↥(Gamma0 L)) (φ : H1 L H 𝒪) :
    diamondRaw L H 𝒪 (σ * τ) φ = diamondRaw L H 𝒪 τ (diamondRaw L H 𝒪 σ φ) := by
  refine AddMonoidHom.ext fun a => ?_
  set γ := Additive.toMul a
  change φ (Additive.ofMul (conjHom L H (σ * τ) γ)) =
    φ (Additive.ofMul (conjHom L H σ (conjHom L H τ γ)))
  have : conjHom L H (σ * τ) γ = conjHom L H σ (conjHom L H τ γ) := by
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
    group
  rw [this]

theorem diamondRaw_eq_self_of_mem (σ : ↥(Gamma0 L)) (hσ : (σ : SL(2, ℤ)) ∈ GammaH L H)
    (φ : H1 L H 𝒪) : diamondRaw L H 𝒪 σ φ = φ := by
  refine AddMonoidHom.ext fun a => ?_
  set γ := Additive.toMul a
  change φ (Additive.ofMul (conjHom L H σ γ)) = φ (Additive.ofMul γ)
  have : conjHom L H σ γ = ⟨σ, hσ⟩ * γ * ⟨σ, hσ⟩⁻¹ := Subtype.ext rfl
  rw [this, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, add_neg_cancel_comm]

theorem diamondL_eq_of_inv_mul_mem {u₁ u₂ : (ZMod L)ˣ} (hu : u₁⁻¹ * u₂ ∈ H) (φ : H1 L H 𝒪) :
    diamondL L H 𝒪 u₂ φ = diamondL L H 𝒪 u₁ φ := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective L u₁
  obtain ⟨τ, hτ⟩ := gamma0Units_surjective L (u₁⁻¹ * u₂)
  have hστ : gamma0Units L (σ * τ) = u₂ := by rw [map_mul, hσ, hτ, mul_inv_cancel_left]
  have hτH : (τ : SL(2, ℤ)) ∈ GammaH L H := mem_GammaH_iff.mpr ⟨τ.2, by
    rw [Subtype.coe_eta, hτ]; exact hu⟩
  rw [diamondL_eq_diamondRaw L H 𝒪 u₂ (σ * τ) hστ, diamondL_eq_diamondRaw L H 𝒪 u₁ σ hσ,
    diamondRaw_mul, diamondRaw_eq_self_of_mem 𝒪 τ hτH]

noncomputable abbrev eIota : ↥(GammaH L H) ≃* ↥((iotaDeg L L H' H 1 h).range) :=
  MonoidHom.ofInjective (iotaDeg_injective L L H' H 1 h)

theorem pushChar_conj (φ : H1 L H 𝒪) (t : ↥(GammaH L H')) (γ : ↥(GammaH L H))
    (hm : t⁻¹ * (iotaDeg L L H' H 1 h γ * t) ∈ (iotaDeg L L H' H 1 h).range) :
    pushChar L L H' H 1 𝒪 h φ (Additive.ofMul (⟨t⁻¹ * (iotaDeg L L H' H 1 h γ * t), hm⟩ :
      ↥((iotaDeg L L H' H 1 h).range))) =
      diamondL L H 𝒪 ((unitsChar L H' t : (ZMod L)ˣ))⁻¹ φ (Additive.ofMul γ) := by
  set σ : ↥(Gamma0 L) := ⟨((t⁻¹ : ↥(GammaH L H')) : SL(2, ℤ)), GammaH_le_Gamma0 H' (t⁻¹).2⟩ with hσ
  have hσu : gamma0Units L σ = ((unitsChar L H' t : (ZMod L)ˣ))⁻¹ := by
    rw [coe_unitsChar, ← map_inv]
    exact congrArg _ (Subtype.ext rfl)
  have hval : (eIota h).symm ⟨_, hm⟩ = conjHom L H σ γ := by
    apply (eIota h).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply, coe_iotaDeg_one]
    show (((t⁻¹ * (iotaDeg L L H' H 1 h γ * t) : ↥(GammaH L H'))) : SL(2, ℤ)) =
      (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_iotaDeg_one, hσ, InvMemClass.coe_inv, inv_inv,
      mul_assoc]
  change φ (Additive.ofMul ((eIota h).symm ⟨_, hm⟩)) = _
  rw [hval, diamondL_eq_diamondRaw L H 𝒪 _ σ hσu]
  rfl

section Main

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem iDeg'_jDeg_apply (φ : H1 L H 𝒪) (γ : ↥(GammaH L H)) :
    iDeg' L L H' H 1 𝒪 h (jDeg L L H' H 1 𝒪 h φ) (Additive.ofMul γ) =
      ∑ q : ↥(GammaH L H') ⧸ (iotaDeg L L H' H 1 h).range,
        diamondL L H 𝒪 ((unitsChar L H'
          ((Subgroup.IsComplement.leftQuotientEquiv
            (default : ((iotaDeg L L H' H 1 h).range).LeftTransversal).2 q :
              ↥((default : ((iotaDeg L L H' H 1 h).range).LeftTransversal).1)) :
            ↥(GammaH L H')) : (ZMod L)ˣ))⁻¹ φ (Additive.ofMul γ) := by
  set R := (iotaDeg L L H' H 1 h).range with hR
  set g : ↥(GammaH L H') := iotaDeg L L H' H 1 h γ with hg
  have hgR : g ∈ R := ⟨γ, rfl⟩
  change jDeg L L H' H 1 𝒪 h φ (Additive.ofMul g) = _
  change ((MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight (pushChar L L H' H 1 𝒪 h φ))) g).toAdd = _
  rw [MonoidHom.transfer_def _ default]
  simp only [Subgroup.leftTransversals.diff, toAdd_prod, AddMonoidHom.toMultiplicativeRight_apply_apply,
    toAdd_ofAdd]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq : g⁻¹ • q = q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
      have : (g⁻¹ * x)⁻¹ * x = x⁻¹ * g * x⁻¹⁻¹ := by group
      rw [this]
      exact Subgroup.Normal.conj_mem inferInstance g hgR x⁻¹
  set t : ↥(GammaH L H') := ((Subgroup.IsComplement.leftQuotientEquiv
    (default : R.LeftTransversal).2 q : ↥((default : R.LeftTransversal).1)) : ↥(GammaH L H')) with ht
  have key : ((Subgroup.IsComplement.leftQuotientEquiv (g • (default : R.LeftTransversal)).2 q :
      ↥((g • (default : R.LeftTransversal)).1)) : ↥(GammaH L H')) = g * t := by
    rw [ht, Subgroup.smul_apply_eq_smul_apply_inv_smul, hq, smul_eq_mul]
  have hm' : t⁻¹ * (g * t) ∈ R := by
    have := Subgroup.Normal.conj_mem inferInstance g hgR t⁻¹
    simpa only [inv_inv, mul_assoc] using this
  have hval : ∀ (hm : t⁻¹ * ((Subgroup.IsComplement.leftQuotientEquiv
      (g • (default : R.LeftTransversal)).2 q : ↥((g • (default : R.LeftTransversal)).1)) :
        ↥(GammaH L H')) ∈ R), (⟨_, hm⟩ : ↥R) = ⟨t⁻¹ * (g * t), hm'⟩ :=
    fun hm => Subtype.ext (by simp only [key])
  rw [hval, pushChar_conj h 𝒪 φ t γ hm']

theorem bijective_reindex :
    Function.Bijective (fun q : ↥(GammaH L H') ⧸ (iotaDeg L L H' H 1 h).range =>
      ((QuotientGroup.mk (unitsChar L H'
        ((Subgroup.IsComplement.leftQuotientEquiv
          (default : ((iotaDeg L L H' H 1 h).range).LeftTransversal).2 q :
            ↥((default : ((iotaDeg L L H' H 1 h).range).LeftTransversal).1)) :
          ↥(GammaH L H'))) : ↥H' ⧸ H.subgroupOf H')⁻¹)) := by
  set R := (iotaDeg L L H' H 1 h).range with hR
  set T : R.LeftTransversal := default with hT
  have hTq : ∀ q : ↥(GammaH L H') ⧸ R,
      (QuotientGroup.mk ((Subgroup.IsComplement.leftQuotientEquiv T.2 q : ↥(T.1)) : ↥(GammaH L H')) :
        ↥(GammaH L H') ⧸ R) = q :=
    fun q => Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv T.2 q
  have hunit : ∀ q₁ q₂ : ↥(GammaH L H') ⧸ R,
      (QuotientGroup.mk (unitsChar L H' ((Subgroup.IsComplement.leftQuotientEquiv T.2 q₁ : ↥(T.1)) :
          ↥(GammaH L H'))) : ↥H' ⧸ H.subgroupOf H') =
        QuotientGroup.mk (unitsChar L H' ((Subgroup.IsComplement.leftQuotientEquiv T.2 q₂ : ↥(T.1)) :
          ↥(GammaH L H'))) ↔ q₁ = q₂ := by
    intro q₁ q₂
    rw [QuotientGroup.eq, ← map_inv, ← map_mul, ← mem_range_iff_unitsChar h, ← hR, ← QuotientGroup.eq,
      hTq, hTq]
  constructor
  · intro q₁ q₂ hq
    have hq' : (QuotientGroup.mk (unitsChar L H' ((Subgroup.IsComplement.leftQuotientEquiv T.2 q₁ :
        ↥(T.1)) : ↥(GammaH L H'))) : ↥H' ⧸ H.subgroupOf H') =
        QuotientGroup.mk (unitsChar L H' ((Subgroup.IsComplement.leftQuotientEquiv T.2 q₂ : ↥(T.1)) :
          ↥(GammaH L H'))) := inv_injective hq
    exact (hunit q₁ q₂).mp hq'
  · intro x
    obtain ⟨σ, hσ⟩ := unitsChar_surjective (L := L) (H' := H') (x⁻¹).out
    refine ⟨QuotientGroup.mk σ, ?_⟩
    show (QuotientGroup.mk (unitsChar L H' ((Subgroup.IsComplement.leftQuotientEquiv T.2
      (QuotientGroup.mk σ) : ↥(T.1)) : ↥(GammaH L H'))) : ↥H' ⧸ H.subgroupOf H')⁻¹ = x
    have hmk : (QuotientGroup.mk (unitsChar L H' σ) : ↥H' ⧸ H.subgroupOf H') = x⁻¹ := by
      rw [hσ, QuotientGroup.out_eq']
    suffices hsuff : (QuotientGroup.mk (unitsChar L H' ((Subgroup.IsComplement.leftQuotientEquiv T.2
        (QuotientGroup.mk σ) : ↥(T.1)) : ↥(GammaH L H'))) : ↥H' ⧸ H.subgroupOf H') = x⁻¹ by
      rw [hsuff]; exact DivisionMonoid.inv_inv x
    rw [← hmk, QuotientGroup.eq, ← map_inv, ← map_mul, ← mem_range_iff_unitsChar h, ← hR,
      ← QuotientGroup.eq, hTq]

theorem main (φ : H1 L H 𝒪) :
    iDeg' L L H' H 1 𝒪 h (jDeg L L H' H 1 𝒪 h φ) =
      ∑ᶠ q : ↥H' ⧸ H.subgroupOf H', diamondL L H 𝒪 ((q.out : ↥H') : (ZMod L)ˣ) φ := by
  classical
  haveI : Fintype (↥H' ⧸ H.subgroupOf H') := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  refine AddMonoidHom.ext fun a => ?_
  set γ := Additive.toMul a
  change iDeg' L L H' H 1 𝒪 h (jDeg L L H' H 1 𝒪 h φ) (Additive.ofMul γ) = _
  rw [iDeg'_jDeg_apply h 𝒪 φ γ, AddMonoidHom.finsetSum_apply]
  refine Fintype.sum_bijective _ (bijective_reindex h) _ _ fun q => ?_

  apply congrArg (fun ψ : H1 L H 𝒪 => ψ (Additive.ofMul γ))
  apply diamondL_eq_of_inv_mul_mem
  set u : ↥H' := unitsChar L H' ((Subgroup.IsComplement.leftQuotientEquiv
    (default : ((iotaDeg L L H' H 1 h).range).LeftTransversal).2 q :
      ↥((default : ((iotaDeg L L H' H 1 h).range).LeftTransversal).1)) : ↥(GammaH L H')) with hu
  set z : ↥H' ⧸ H.subgroupOf H' := (QuotientGroup.mk u : ↥H' ⧸ H.subgroupOf H')⁻¹ with hz
  have hzout : (QuotientGroup.mk z.out : ↥H' ⧸ H.subgroupOf H') = QuotientGroup.mk u⁻¹ := by
    rw [QuotientGroup.out_eq', hz, QuotientGroup.mk_inv]
  have hmem := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hzout)
  rwa [Subgroup.coe_mul, InvMemClass.coe_inv, InvMemClass.coe_inv] at hmem

end Main

end NormSol
p2m_reactivate "P2MW.S_CohCarrier_iDegP_jDeg_eq_finsum_diamondL.NormSol"

theorem solution
    (L : ℕ) [NeZero L] (𝒪 : Type) [CommRing 𝒪]
    (H H' : Subgroup (ZMod L)ˣ) (h : CohCarrier.LevelLE L L H' H 1) (φ : CohCarrier.H1 L H 𝒪) :
    CohCarrier.iDeg' L L H' H 1 𝒪 h (CohCarrier.jDeg L L H' H 1 𝒪 h φ) =
      ∑ᶠ q : ↥H' ⧸ H.subgroupOf H', CohCarrier.diamondL L H 𝒪 ((q.out : ↥H') : (ZMod L)ˣ) φ :=
  NormSol.main h 𝒪 φ

end S_CohCarrier_iDegP_jDeg_eq_finsum_diamondL
end P2MW
export P2MW.S_CohCarrier_iDegP_jDeg_eq_finsum_diamondL (solution)
