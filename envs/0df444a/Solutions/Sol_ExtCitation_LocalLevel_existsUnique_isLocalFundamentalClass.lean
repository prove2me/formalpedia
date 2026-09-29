-- Prove2me | solution 1 for ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7e4164c3-bab8-5da7-b9c3-378d23f82d04

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1
import Theorems.Thm_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units
import Theorems.Thm_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level
import Theorems.Thm_ExtCitation_LocalLevel_exists_overlayer_unramified_level
import Theorems.Thm_ExtCitation_LocalLevel_isLocalFundamentalClass_of_pin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel"

noncomputable section
namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.range_infNatTrans_eq_of_unramified_level LocalLevel.exists_overlayer_unramified_level LocalLevel.isLocalFundamentalClass_of_pin"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass isZero_groupCohomology_one_res_units range_infNatTrans_eq_of_unramified_level exists_overlayer_unramified_level isLocalFundamentalClass_of_pin"
namespace Ws25C6
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
variable {G : Type} [Group G] [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ]
variable {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
variable {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
variable {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
variable {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}

section back
variable (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
variable (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π)
include hcompat d

abbrev uM (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : (↥M)ˣ := Additive.toMul (v.1 : Additive (↥M)ˣ)

omit hcompat d in
theorem uM_add (v w : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : uM (v + w) = uM v * uM w := rfl

theorem mem_L_uM (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    (((uM v : (↥M)ˣ) : M) : PadicAlgCl q) ∈ L := by
  rw [d.mem_layer_iff]
  intro h hh
  have h2 : h • (uM v) = uM v := congrArg Additive.toMul (v.2 ⟨h, hh⟩)
  calc h • ((uM v : (↥M)ˣ) : M) = ((h • uM v : (↥M)ˣ) : M) := (d.coe_smul_units h (uM v)).symm
    _ = ((uM v : (↥M)ˣ) : M) := by rw [h2]

def xL (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : L := ⟨_, mem_L_uM hcompat d v⟩

@[scoped simp] theorem coe_xL (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    ((xL hcompat d v : L) : PadicAlgCl q) = (((uM v : (↥M)ˣ) : M) : PadicAlgCl q) := rfl

theorem xL_ne_zero (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : xL hcompat d v ≠ 0 := by
  intro h0
  have h1 : (((uM v : (↥M)ˣ) : M) : PadicAlgCl q) = 0 := by rw [← coe_xL hcompat d v, h0]; rfl
  have h2 : ((uM v : (↥M)ˣ) : M) = 0 := Subtype.ext h1
  exact (uM v).ne_zero h2

theorem xL_add (v w : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    xL hcompat d (v + w) = xL hcompat d v * xL hcompat d w := by
  apply Subtype.ext
  show (((uM (v + w) : (↥M)ˣ) : M) : PadicAlgCl q) = ((xL hcompat d v : L) : PadicAlgCl q) * ((xL hcompat d w : L) : PadicAlgCl q)
  rw [coe_xL, coe_xL, uM_add, Units.val_mul]
  rfl

def backUnit (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : (↥L)ˣ :=
  Units.mk0 (xL hcompat d v) (xL_ne_zero hcompat d v)

@[scoped simp] theorem val_backUnit (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    ((backUnit hcompat d v : (↥L)ˣ) : L) = xL hcompat d v := rfl

theorem backUnit_add (v w : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    backUnit hcompat d (v + w) = backUnit hcompat d v * backUnit hcompat d w := by
  apply Units.ext
  rw [Units.val_mul, val_backUnit, val_backUnit, val_backUnit, xL_add]

def backAdd : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL →+ Additive (↥L)ˣ where
  toFun v := Additive.ofMul (backUnit hcompat d v)
  map_zero' := by
    show Additive.ofMul (backUnit hcompat d 0) = 0
    have : backUnit hcompat d 0 = 1 := by
      have h := backUnit_add hcompat d 0 0
      rw [add_zero] at h
      exact mul_left_cancel (a := backUnit hcompat d 0) (by rw [← h, mul_one])
    rw [this]; rfl
  map_add' v w := by
    show Additive.ofMul (backUnit hcompat d (v + w)) = Additive.ofMul (backUnit hcompat d v) + Additive.ofMul (backUnit hcompat d w)
    rw [backUnit_add]; rfl

theorem backAdd_apply (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    backAdd hcompat d v = Additive.ofMul (backUnit hcompat d v) := rfl

theorem backUnit_smul (g : G) (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    backUnit hcompat d (((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL).ρ (e g) v) = g • backUnit hcompat d v := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e g)
  apply Units.ext
  apply Subtype.ext
  rw [hcompat, val_backUnit, val_backUnit, coe_xL, d.coe_smul_eq g h hh (xL hcompat d v)]
  have hx : (⟨((xL hcompat d v : L) : PadicAlgCl q), hLM (xL hcompat d v).2⟩ : M) = ((uM v : (↥M)ˣ) : M) := Subtype.ext rfl
  rw [hx, ← d.coe_smul_units]

  have hρ : uM (((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL).ρ (e g) v) = h • uM v := by
    rw [← hh]; rfl
  rw [hρ]

def back : Rep.res e.toMonoidHom ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) ⟶ Rep.ofMulDistribMulAction G (↥L)ˣ :=
  Rep.ofHom
    { (backAdd hcompat d).toIntLinearMap with
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        show Additive.ofMul (backUnit hcompat d (((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL).ρ (e g) v)) =
          Additive.ofMul (g • backUnit hcompat d v)
        rw [backUnit_smul] }

theorem back_hom_apply (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    (back hcompat d).hom v = Additive.ofMul (backUnit hcompat d v) := rfl

end back

end ExtCitation.LocalLevel.Ws25C6
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation"
end
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.range_infNatTrans_eq_of_unramified_level LocalLevel.exists_overlayer_unramified_level LocalLevel.isLocalFundamentalClass_of_pin"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass isZero_groupCohomology_one_res_units range_infNatTrans_eq_of_unramified_level exists_overlayer_unramified_level isLocalFundamentalClass_of_pin"
namespace Ws25C6
p2m_open "ExtCitation.LocalLevel ExtCitation"

theorem exists_pin (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
    {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}
    (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π) :
    ∃ u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ),
      ∀ (ι : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction H (↥M)ˣ),
        (∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q)) →
        ∀ (hfin : IsOfFinOrder (QuotientGroup.mk' Nn φ))
          (hc : carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)),
          (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι 2).hom u =
            ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
              ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
                ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩) := by
  classical

  have hH := d.smul_algebraMap
  have hHcompat := d.coe_smul_units

  haveI : Group.IsSolvable G := hsolv
  haveI : Group.IsSolvable (H ⧸ NL) := solvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hcardG : Nat.card G = Nat.card (H ⧸ NL) := Nat.card_congr e.toEquiv
  have hcard : Nat.card (H ⧸ Nn) = Nat.card (H ⧸ NL) := d.card_quotient.trans hcardG
  have hrange := ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level q M H hH hHcompat NL inferInstance Nn hcard π
    d.smul_pi d.norm_pi_lt d.norm_le_norm_pi

  have hfin₀ : IsOfFinOrder (QuotientGroup.mk' Nn φ) := isOfFinOrder_of_finite _
  have hc₀ : carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin₀ d.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn) := by
    refine groupCohomology.carryFun_mem_cocycles2 _ _ _ _ (Subtype.ext ?_)
    exact congrArg Additive.ofMul (d.smul_pi φ)

  have hmem : ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
      ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin₀ d.piInv, hc₀⟩) ∈
      LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ))) := by
    rw [hrange]; exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hmem

  obtain ⟨cv, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL))).mp inferInstance v

  refine ⟨(groupCohomology.map e.toMonoidHom (back hcompat d) 2).hom ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL)).hom cv), ?_⟩
  intro ι hι hfin hc

  have hirr : (⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩ : cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)) =
      ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin₀ d.piInv, hc₀⟩ := Subtype.ext rfl
  rw [hirr, ← hv]

  change (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι 2).hom
      ((groupCohomology.map e.toMonoidHom (back hcompat d) 2).hom ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL)).hom cv)) =
    (groupCohomology.map (QuotientGroup.mk' NL) (Rep.ofHom ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.quotientToInvariants_lift NL)) 2).hom
      ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL)).hom cv)
  rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply]
  refine congrArg ((H2π (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom) (Subtype.ext (funext fun p => ?_))
  obtain ⟨h₁, h₂⟩ := p

  show ι.hom ((back hcompat d).hom (cv (e (e.symm (QuotientGroup.mk h₁)), e (e.symm (QuotientGroup.mk h₂))))) =
    ((cv (QuotientGroup.mk h₁, QuotientGroup.mk h₂)).1 : Additive (↥M)ˣ)
  rw [e.apply_symm_apply, e.apply_symm_apply, back_hom_apply]

  have key : Additive.toMul (ι.hom (Additive.ofMul (backUnit hcompat d (cv (QuotientGroup.mk h₁, QuotientGroup.mk h₂))))) =
      uM (cv (QuotientGroup.mk h₁, QuotientGroup.mk h₂)) := by
    apply Units.ext; apply Subtype.ext
    exact (hι (backUnit hcompat d (cv (QuotientGroup.mk h₁, QuotientGroup.mk h₂)))).trans rfl
  exact congrArg Additive.ofMul key

end ExtCitation.LocalLevel.Ws25C6
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.range_infNatTrans_eq_of_unramified_level LocalLevel.exists_overlayer_unramified_level LocalLevel.isLocalFundamentalClass_of_pin"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass isZero_groupCohomology_one_res_units range_infNatTrans_eq_of_unramified_level exists_overlayer_unramified_level isLocalFundamentalClass_of_pin"
namespace Ws25C6
p2m_open "ExtCitation.LocalLevel ExtCitation"
noncomputable section

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

omit hcompat d in
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

theorem fwd_hom_apply (v : (↥L)ˣ) : (fwd hcompat d).hom (Additive.ofMul v) = Additive.ofMul (fwdUnit (hLM := hLM) v) := rfl

theorem fwd_char (v : (↥L)ˣ) : (((Additive.toMul ((fwd hcompat d).hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q) := rfl

theorem backUnit_fwd (v : (↥L)ˣ) (hv : (fwd hcompat d).hom (Additive.ofMul v) ∈ Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp NL.subtype)) :
    backUnit hcompat d ⟨(fwd hcompat d).hom (Additive.ofMul v), hv⟩ = v := by
  apply Units.ext; apply Subtype.ext
  rfl

theorem fwd_mem_invariants (v : Additive (↥L)ˣ) :
    (fwd hcompat d).hom v ∈ Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp NL.subtype) := by
  obtain ⟨w, rfl⟩ : ∃ w : (↥L)ˣ, Additive.ofMul w = v := ⟨Additive.toMul v, rfl⟩
  intro n
  show Additive.ofMul ((n : H) • fwdUnit (hLM := hLM) w) = Additive.ofMul (fwdUnit (hLM := hLM) w)
  congr 1
  apply Units.ext
  rw [d.coe_smul_units]
  exact (d.mem_layer_iff ((fwdUnit (hLM := hLM) w : (↥M)ˣ) : M)).mp (w : L).2 n n.2

def fwd' : Rep.res e.symm.toMonoidHom (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL :=
  Rep.ofHom
    { ({ toFun := fun v => ⟨(fwd hcompat d).hom v, fwd_mem_invariants hcompat d v⟩
         map_zero' := Subtype.ext ((fwd hcompat d).hom.toLinearMap.map_zero)
         map_add' := fun v w => Subtype.ext ((fwd hcompat d).hom.toLinearMap.map_add v w) } :
          Additive (↥L)ˣ →+ (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL).toIntLinearMap with
      isIntertwining' := by
        intro a
        induction a using QuotientGroup.induction_on with
        | H h =>
          apply LinearMap.ext
          intro v
          apply Subtype.ext
          exact congrArg (fun ψ : _ →ₗ[ℤ] _ => ψ v) ((fwd hcompat d).hom.isIntertwining' h) }

theorem fwd'_val (v : Additive (↥L)ˣ) : (((fwd' hcompat d).hom v).1 : Additive (↥M)ˣ) = (fwd hcompat d).hom v := rfl

theorem map_fwd_eq_inf_map (c : cocycles₂ (Rep.ofMulDistribMulAction G (↥L)ˣ)) :
    (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat d) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c) =
      ((infNatTrans ℤ NL 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
        ((groupCohomology.map e.symm.toMonoidHom (fwd' hcompat d) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c)) := by
  change _ = (groupCohomology.map (QuotientGroup.mk' NL) (Rep.ofHom ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.quotientToInvariants_lift NL)) 2).hom
      ((groupCohomology.map e.symm.toMonoidHom (fwd' hcompat d) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c))
  rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply]
  exact congrArg ((H2π (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom) (Subtype.ext (funext fun p => rfl))

theorem map_back_map_fwd' (c : cocycles₂ (Rep.ofMulDistribMulAction G (↥L)ˣ)) :
    (groupCohomology.map e.toMonoidHom (back hcompat d) 2).hom
        ((groupCohomology.map e.symm.toMonoidHom (fwd' hcompat d) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c)) =
      (H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c := by
  rw [H2π_comp_map_apply, H2π_comp_map_apply]
  refine congrArg ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom) (Subtype.ext (funext fun p => ?_))
  obtain ⟨g₁, g₂⟩ := p
  show (back hcompat d).hom ((fwd' hcompat d).hom (c (e.symm (e g₁), e.symm (e g₂)))) = c (g₁, g₂)
  rw [e.symm_apply_apply, e.symm_apply_apply, back_hom_apply]
  obtain ⟨w, hw⟩ : ∃ w : (↥L)ˣ, Additive.ofMul w = c (g₁, g₂) := ⟨Additive.toMul (c (g₁, g₂)), rfl⟩
  rw [← hw]
  exact congrArg Additive.ofMul (backUnit_fwd hcompat d w _)

theorem map_fwd_injective :
    Function.Injective (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat d) 2).hom := by
  classical
  have h90 := ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units q M H d.smul_algebraMap d.coe_smul_units (↥NL) NL.subtype
    Subtype.val_injective
  have hinj₀ := (groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 (Rep.ofMulDistribMulAction H (↥M)ˣ) NL h90).1
  have hinj : Function.Injective ((infNatTrans ℤ NL 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom := hinj₀
  intro x y hxy
  obtain ⟨cx, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π (Rep.ofMulDistribMulAction G (↥L)ˣ))).mp inferInstance x
  obtain ⟨cy, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π (Rep.ofMulDistribMulAction G (↥L)ˣ))).mp inferInstance y
  rw [map_fwd_eq_inf_map, map_fwd_eq_inf_map] at hxy
  have h2 := hinj hxy
  rw [← map_back_map_fwd' hcompat d cx, ← map_back_map_fwd' hcompat d cy, h2]

end
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"
end ExtCitation.LocalLevel.Ws25C6
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass.ExtCitation.LocalLevel.Ws25C6"

open ExtCitation.LocalLevel.Ws25C6 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K) :
    ∃! u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ), IsLocalFundamentalClass q L G K u := by
  classical

  obtain ⟨M, _, hLM, H, _, _, _, _, _, NL, Nn, _, _, e, φ, π, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    ExtCitation.LocalLevel.exists_overlayer_unramified_level q L G hG hcompat K hK.le hK.mem_iff (Nat.card G) Nat.card_pos
  have d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π :=
    { smul_algebraMap := h1, coe_smul_units := h2, mem_base_iff := h3, mem_layer_iff := h4, coe_smul_eq := h5,
      card_quotient := h6, mem_zpowers := h7, frobenius := h8, smul_pi := h9, pi_mem := h10, norm_pi_lt := h11,
      norm_le_norm_pi := h12 }

  obtain ⟨u, hu⟩ := exists_pin q L G hG hcompat hsolv K d
  refine ⟨u, ExtCitation.LocalLevel.isLocalFundamentalClass_of_pin q L G hG hcompat K hK d u hu, ?_⟩

  intro u' hu'
  have hfin : IsOfFinOrder (QuotientGroup.mk' Nn φ) := isOfFinOrder_of_finite _
  have hc : carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn) := by
    refine groupCohomology.carryFun_mem_cocycles2 _ _ _ _ (Subtype.ext ?_)
    exact congrArg Additive.ofMul (d.smul_pi φ)
  have e1 := hu' M hLM H NL Nn e φ π d (fwd hcompat d) (fwd_char hcompat d) hfin hc
  have e2 := hu (fwd hcompat d) (fwd_char hcompat d) hfin hc
  exact map_fwd_injective hcompat d (e1.trans e2.symm)

end S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
end P2MW
export P2MW.S_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass (solution)
