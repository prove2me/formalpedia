-- Prove2me | solution 1 for ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/259acdcc-d611-54b4-9db7-540ffef60355

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_Corestriction2
import Theorems.Thm_ExtCitation_LocalLevel_exists_overlayer_unramified_level
import Theorems.Thm_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units
import Theorems.Thm_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
import Theorems.Thm_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable
import Theorems.Thm_groupCohomology_Cores_cores_map_res_eq_index_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation.LocalLevel"

attribute [local instance] groupCohomology.Cores.fintypeQuot

noncomputable section
namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_overlayer_unramified_level LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass exists_overlayer_unramified_level isZero_groupCohomology_one_res_units exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun finite_H2_units_and_natCard_le_of_isSolvable"
namespace Ws25C6b
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
variable {G : Type} [Group G] [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ]
variable {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
variable {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
variable {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
variable {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}
variable (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
variable (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π)
include hcompat d

def fwdUnit (v : (↥L)ˣ) : (↥M)ˣ := Units.map (IntermediateField.inclusion hLM).toMonoidHom v

omit [FiniteDimensional ℚ_[q] M] hcompat d in
@[scoped simp] theorem coe_fwdUnit (v : (↥L)ˣ) : (((fwdUnit (hLM := hLM) v : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q) := rfl

def fwd : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction H (↥M)ˣ :=
  Rep.ofHom
    { (MonoidHom.toAdditive (Units.map (IntermediateField.inclusion hLM).toMonoidHom)).toIntLinearMap with
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro v
        obtain ⟨w, rfl⟩ : ∃ w : (↥L)ˣ, Additive.ofMul w = v := ⟨Additive.toMul v, rfl⟩
        set g : G := e.symm (QuotientGroup.mk h : H ⧸ NL) with hg
        show Additive.ofMul (fwdUnit (hLM := hLM) (g • w)) = Additive.ofMul (h • fwdUnit (hLM := hLM) w)
        congr 1
        apply Units.ext; apply Subtype.ext
        rw [d.coe_smul_units, coe_fwdUnit, hcompat]
        have hh : (QuotientGroup.mk h : H ⧸ NL) = e g := by rw [hg, e.apply_symm_apply]
        rw [d.coe_smul_eq g h hh]
        rfl }

theorem fwd_char (v : (↥L)ˣ) : (((Additive.toMul ((fwd hcompat d).hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q) := rfl

end ExtCitation.LocalLevel.Ws25C6b
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6b"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation.LocalLevel"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation"
end
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6b"

open ExtCitation.LocalLevel.Ws25C6b in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : IsLocalFundamentalClass q L G K u) :
    (∀ S : Subgroup G, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 1)) ∧
    (∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G, Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom u} = ⊤) := by
  classical
  haveI : Group.IsSolvable G := hsolv

  obtain ⟨M, _, hLM, H, _, _, _, _, _, NL, Nn, _, _, e, φ, π, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    ExtCitation.LocalLevel.exists_overlayer_unramified_level q L G hG hcompat K hK.le hK.mem_iff (Nat.card G) Nat.card_pos
  have d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π :=
    { smul_algebraMap := h1, coe_smul_units := h2, mem_base_iff := h3, mem_layer_iff := h4, coe_smul_eq := h5,
      card_quotient := h6, mem_zpowers := h7, frobenius := h8, smul_pi := h9, pi_mem := h10, norm_pi_lt := h11,
      norm_le_norm_pi := h12 }
  have hfin : IsOfFinOrder (QuotientGroup.mk' Nn φ) := isOfFinOrder_of_finite _
  have hc : carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn) := by
    refine groupCohomology.carryFun_mem_cocycles2 _ _ _ _ (Subtype.ext ?_)
    exact congrArg Additive.ofMul (d.smul_pi φ)
  have hpin := hu M hLM H NL Nn e φ π d (fwd hcompat d) (fwd_char hcompat d) hfin hc

  have h90 := ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units q M H d.smul_algebraMap d.coe_smul_units (↥Nn) Nn.subtype
    Subtype.val_injective
  have hinj₀ := (groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 (Rep.ofMulDistribMulAction H (↥M)ˣ) Nn h90).1
  have hinj : Function.Injective ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom := hinj₀

  obtain ⟨inv, hinv⟩ := ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun q M H
    d.smul_algebraMap d.coe_smul_units Nn φ d.mem_zpowers hfin π d.smul_pi d.norm_pi_lt d.norm_le_norm_pi
  have hval : inv ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
      ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩) = ((1 : ℤ) : ZMod (Nat.card (H ⧸ Nn))) :=
    hinv d.piInv 1 hc (by rw [zpow_one]; rfl)

  have hFinf : ∀ (k : ℕ) (y : groupCohomology.H2 ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)),
      ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom (k • y) =
        k • ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom y := fun k y => map_nsmul _ k y
  have hFinf0 : ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
      (0 : groupCohomology.H2 ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)) = 0 := map_zero _
  have hFpin : ∀ (k : ℕ) (y : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)),
      (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat d) 2).hom (k • y) =
        k • (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat d) 2).hom y := fun k y => map_nsmul _ k y
  have hFpin0 : (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat d) 2).hom
      (0 : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) = 0 := map_zero _
  have hdivG : ∀ k : ℕ, k • u = 0 → Nat.card G ∣ k := by
    intro k hk
    have h0 : ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
        (k • (H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
          ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩) = 0 :=
      calc ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
            (k • (H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
              ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩)
          = k • ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
              ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
                ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩) := hFinf k _
        _ = k • (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat d) 2).hom u :=
            congrArg (fun z => k • z) hpin.symm
        _ = (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat d) 2).hom (k • u) := (hFpin k u).symm
        _ = 0 := by rw [hk]; exact hFpin0
    have h1 : k • (H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
        ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩ = 0 :=
      hinj (by rw [h0, hFinf0])
    have h2 := congrArg inv h1
    rw [map_nsmul, hval, map_zero, Int.cast_one, nsmul_one, ZMod.natCast_eq_zero_iff] at h2
    rw [← d.card_quotient]
    exact h2

  have main : ∀ S : Subgroup G,
      CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 1) ∧
      (Finite (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) ∧
        Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) = Nat.card S) ∧
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom u} = ⊤ := by
    intro S

    have hS90 := ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units q L G hG hcompat (↥S) S.subtype Subtype.val_injective

    letI : MulDistribMulAction S (↥L)ˣ := MulDistribMulAction.compHom (↥L)ˣ S.subtype
    haveI : FaithfulSMul S L :=
      ⟨fun {s t} h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) (fun x => h x))⟩
    have hres : Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ) = Rep.ofMulDistribMulAction S (↥L)ˣ := rfl
    have hbound := ExtCitation.LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable q L (↥S) inferInstance
      (fun s x => hG s x) (fun s v => hcompat s v)
    rw [← hres] at hbound
    obtain ⟨hfinS, hle⟩ := hbound
    haveI := hfinS

    obtain ⟨r, hr⟩ : ∃ r : groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2,
        r = (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom u := ⟨_, rfl⟩

    haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨τ⟩ := groupCohomology.Cores.Transversal.nonempty (H := S)
    have hcor : groupCohomology.Cores.cores (Rep.ofMulDistribMulAction G (↥L)ˣ) τ r = S.index • u := by
      rw [hr]; exact groupCohomology.Cores.cores_map_res_eq_index_smul _ S τ u
    have hdivS : ∀ k : ℕ, k • r = 0 → Nat.card S ∣ k := by
      intro k hk
      have : (k * S.index) • u = 0 := by
        rw [mul_comm, mul_nsmul, ← hcor, ← map_nsmul, hk, map_zero]
      have hG' := hdivG _ this
      rw [← Subgroup.card_mul_index S] at hG'
      exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) hG'

    have hord_dvd : Nat.card S ∣ addOrderOf r := hdivS _ (addOrderOf_nsmul_eq_zero r)
    have hord_pos : 0 < addOrderOf r := (isOfFinAddOrder_of_finite r).addOrderOf_pos
    have hord_le : addOrderOf r ≤ Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) := by
      rw [← Nat.card_zmultiples]; exact AddSubgroup.card_le_card_addGroup _
    have hSle : Nat.card S ≤ addOrderOf r := Nat.le_of_dvd hord_pos hord_dvd
    have hle' : Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) ≤ Nat.card S := hle
    have hcardEq : Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) = Nat.card S := by omega
    have hordEq : addOrderOf r = Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) := by omega
    have htop : AddSubgroup.zmultiples r = ⊤ :=
      AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, hordEq])
    refine ⟨hS90, ⟨hfinS, hcardEq⟩, ?_⟩
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ AddSubgroup.zmultiples r := by rw [htop]; exact AddSubgroup.mem_top x
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [← hr]
    refine Submodule.mem_span_singleton.mpr ⟨n, ?_⟩
    exact int_smul_eq_zsmul _ n r
  refine ⟨fun S => (main S).1, fun S _ => ?_, fun S => (main S).2.2⟩
  rw [(main S).2.1.2, Nat.card_eq_fintype_card]

end S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
end P2MW
export P2MW.S_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass (solution)
