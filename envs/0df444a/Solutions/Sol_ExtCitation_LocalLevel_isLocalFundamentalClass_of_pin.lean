-- Prove2me | solution 1 for ExtCitation.LocalLevel.isLocalFundamentalClass_of_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7a7c2d67-ec09-52a5-81dd-007c70ec104c

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_carry_H2pi_add
import Theorems.Thm_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1
import Theorems.Thm_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units
import Theorems.Thm_ExtCitation_LocalLevel_exists_common_overlayer
import Theorems.Thm_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq
import Theorems.Thm_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one
import Theorems.Thm_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_of_pin
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_of_pin.ExtCitation.LocalLevel"

noncomputable section
namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_common_overlayer LocalLevel.eq_of_unramified_level_of_index_eq LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass Rw isZero_groupCohomology_one_res_units exists_common_overlayer eq_of_unramified_level_of_index_eq mem_of_unramified_level_of_forall_norm_smul_sub_lt_one exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace Ws25IND
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]

structure OL (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G : Type) [Group G] [MulSemiringAction G L]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) (hLM : L ≤ M)
    (H : Type) [Group H] [MulSemiringAction H M] [MulDistribMulAction H (↥M)ˣ]
    (NL : Subgroup H) [NL.Normal] (e : G ≃* H ⧸ NL) : Prop where
  smul_algebraMap : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x
  coe_smul_units : ∀ (h : H) (u : (↥M)ˣ), ((h • u : (↥M)ˣ) : M) = h • (u : M)
  mem_layer_iff : ∀ x : M, (x : PadicAlgCl q) ∈ L ↔ ∀ h ∈ NL, h • x = x
  coe_smul_eq : ∀ (g : G) (h : H), (QuotientGroup.mk h : H ⧸ NL) = e g →
    ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q)

variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
variable {G : Type} [Group G] [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ]
variable {M : IntermediateField ℚ_[q] (PadicAlgCl q)} {hLM : L ≤ M}
variable {H : Type} [Group H] [MulSemiringAction H M] [MulDistribMulAction H (↥M)ˣ]
variable {NL : Subgroup H} [NL.Normal] {e : G ≃* H ⧸ NL}
variable (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
variable (o : OL L G M hLM H NL e)
include hcompat o

abbrev fwdUnit (v : (↥L)ˣ) : (↥M)ˣ := Units.map (IntermediateField.inclusion hLM).toMonoidHom v

omit hcompat o in
theorem coe_fwdUnit (v : (↥L)ˣ) : (((fwdUnit (hLM := hLM) v : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q) := rfl

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
        rw [o.coe_smul_units, coe_fwdUnit, hcompat]
        have hh : (QuotientGroup.mk h : H ⧸ NL) = e g := by rw [hg, e.apply_symm_apply]
        rw [o.coe_smul_eq g h hh]
        rfl }

theorem fwd_hom_apply (v : (↥L)ˣ) : (fwd hcompat o).hom (Additive.ofMul v) = Additive.ofMul (fwdUnit (hLM := hLM) v) := rfl

theorem fwd_char (v : (↥L)ˣ) : (((Additive.toMul ((fwd hcompat o).hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q) := rfl

theorem eq_fwd (ι : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction H (↥M)ˣ)
    (hι : ∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q))
    (v : (↥L)ˣ) : ι.hom (Additive.ofMul v) = (fwd hcompat o).hom (Additive.ofMul v) := by
  have : Additive.toMul (ι.hom (Additive.ofMul v)) = fwdUnit (hLM := hLM) v := by
    apply Units.ext; apply Subtype.ext
    exact hι v
  exact congrArg Additive.ofMul this

theorem fwd_mem_invariants (v : Additive (↥L)ˣ) :
    (fwd hcompat o).hom v ∈ Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp NL.subtype) := by
  obtain ⟨w, rfl⟩ : ∃ w : (↥L)ˣ, Additive.ofMul w = v := ⟨Additive.toMul v, rfl⟩
  intro n
  show Additive.ofMul ((n : H) • fwdUnit (hLM := hLM) w) = Additive.ofMul (fwdUnit (hLM := hLM) w)
  congr 1
  apply Units.ext
  rw [o.coe_smul_units]
  exact (o.mem_layer_iff ((fwdUnit (hLM := hLM) w : (↥M)ˣ) : M)).mp (w : L).2 n n.2

def fwd' : Rep.res e.symm.toMonoidHom (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL :=
  Rep.ofHom
    { ({ toFun := fun v => ⟨(fwd hcompat o).hom v, fwd_mem_invariants hcompat o v⟩
         map_zero' := Subtype.ext ((fwd hcompat o).hom.toLinearMap.map_zero)
         map_add' := fun v w => Subtype.ext ((fwd hcompat o).hom.toLinearMap.map_add v w) } :
          Additive (↥L)ˣ →+ (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL).toIntLinearMap with
      isIntertwining' := by
        intro a
        induction a using QuotientGroup.induction_on with
        | H h =>
          apply LinearMap.ext
          intro v
          apply Subtype.ext
          exact congrArg (fun ψ : _ →ₗ[ℤ] _ => ψ v) ((fwd hcompat o).hom.isIntertwining' h) }

omit hcompat o in

abbrev uM (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : (↥M)ˣ := Additive.toMul (v.1 : Additive (↥M)ˣ)

theorem mem_L_uM (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    (((uM v : (↥M)ˣ) : M) : PadicAlgCl q) ∈ L := by
  rw [o.mem_layer_iff]
  intro h hh
  have h2 : h • (uM v) = uM v := congrArg Additive.toMul (v.2 ⟨h, hh⟩)
  calc h • ((uM v : (↥M)ˣ) : M) = ((h • uM v : (↥M)ˣ) : M) := (o.coe_smul_units h (uM v)).symm
    _ = ((uM v : (↥M)ˣ) : M) := by rw [h2]

def xL (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : L := ⟨_, mem_L_uM hcompat o v⟩

theorem coe_xL (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    ((xL hcompat o v : L) : PadicAlgCl q) = (((uM v : (↥M)ˣ) : M) : PadicAlgCl q) := rfl

theorem xL_ne_zero (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : xL hcompat o v ≠ 0 := by
  intro h0
  have h1 : (((uM v : (↥M)ˣ) : M) : PadicAlgCl q) = 0 := by rw [← coe_xL hcompat o v, h0]; rfl
  exact (uM v).ne_zero (Subtype.ext h1)

def backUnit (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) : (↥L)ˣ :=
  Units.mk0 (xL hcompat o v) (xL_ne_zero hcompat o v)

theorem backUnit_fwd (w : (↥L)ˣ) (hw) : backUnit hcompat o ⟨(fwd hcompat o).hom (Additive.ofMul w), hw⟩ = w := by
  apply Units.ext; apply Subtype.ext; rfl

theorem fwd_backUnit (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    (fwd hcompat o).hom (Additive.ofMul (backUnit hcompat o v)) = (v.1 : Additive (↥M)ˣ) := by
  have : fwdUnit (hLM := hLM) (backUnit hcompat o v) = uM v := by
    apply Units.ext; apply Subtype.ext; rfl
  exact congrArg Additive.ofMul this

theorem map_fwd_eq_inf_map (c : cocycles₂ (Rep.ofMulDistribMulAction G (↥L)ˣ)) :
    (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat o) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c) =
      ((infNatTrans ℤ NL 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
        ((groupCohomology.map e.symm.toMonoidHom (fwd' hcompat o) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c)) := by
  change _ = (groupCohomology.map (QuotientGroup.mk' NL) (Rep.ofHom ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.quotientToInvariants_lift NL)) 2).hom
      ((groupCohomology.map e.symm.toMonoidHom (fwd' hcompat o) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c))
  rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply]
  exact congrArg ((H2π (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom) (Subtype.ext (funext fun p => rfl))

theorem xL_add (v w : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    xL hcompat o (v + w) = xL hcompat o v * xL hcompat o w := by
  apply Subtype.ext
  show (((uM (v + w) : (↥M)ˣ) : M) : PadicAlgCl q) = ((xL hcompat o v : L) : PadicAlgCl q) * ((xL hcompat o w : L) : PadicAlgCl q)
  rw [coe_xL, coe_xL, show uM (v + w) = uM v * uM w from rfl, Units.val_mul]
  rfl

theorem val_backUnit (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    ((backUnit hcompat o v : (↥L)ˣ) : L) = xL hcompat o v := rfl

theorem backUnit_add (v w : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    backUnit hcompat o (v + w) = backUnit hcompat o v * backUnit hcompat o w := by
  apply Units.ext
  rw [Units.val_mul, val_backUnit, val_backUnit, val_backUnit, xL_add]

def backAdd : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL →+ Additive (↥L)ˣ where
  toFun v := Additive.ofMul (backUnit hcompat o v)
  map_zero' := by
    show Additive.ofMul (backUnit hcompat o 0) = 0
    have : backUnit hcompat o 0 = 1 := by
      have h := backUnit_add hcompat o 0 0
      rw [add_zero] at h
      exact mul_left_cancel (a := backUnit hcompat o 0) (by rw [← h, mul_one])
    rw [this]; rfl
  map_add' v w := by
    show Additive.ofMul (backUnit hcompat o (v + w)) = Additive.ofMul (backUnit hcompat o v) + Additive.ofMul (backUnit hcompat o w)
    rw [backUnit_add]; rfl

theorem backUnit_smul (g : G) (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    backUnit hcompat o (((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL).ρ (e g) v) = g • backUnit hcompat o v := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e g)
  apply Units.ext
  apply Subtype.ext
  rw [hcompat, val_backUnit, val_backUnit, coe_xL, o.coe_smul_eq g h hh (xL hcompat o v)]
  have hx : (⟨((xL hcompat o v : L) : PadicAlgCl q), hLM (xL hcompat o v).2⟩ : M) = ((uM v : (↥M)ˣ) : M) := Subtype.ext rfl
  rw [hx, ← o.coe_smul_units]
  have hρ : uM (((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL).ρ (e g) v) = h • uM v := by
    rw [← hh]; rfl
  rw [hρ]

def back : Rep.res e.toMonoidHom ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) ⟶ Rep.ofMulDistribMulAction G (↥L)ˣ :=
  Rep.ofHom
    { (backAdd hcompat o).toIntLinearMap with
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        show Additive.ofMul (backUnit hcompat o (((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL).ρ (e g) v)) =
          Additive.ofMul (g • backUnit hcompat o v)
        rw [backUnit_smul] }

theorem back_hom_apply (v : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants NL) :
    (back hcompat o).hom v = Additive.ofMul (backUnit hcompat o v) := rfl

theorem map_back_map_fwd' (c : cocycles₂ (Rep.ofMulDistribMulAction G (↥L)ˣ)) :
    (groupCohomology.map e.toMonoidHom (back hcompat o) 2).hom
        ((groupCohomology.map e.symm.toMonoidHom (fwd' hcompat o) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c)) =
      (H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c := by
  rw [H2π_comp_map_apply, H2π_comp_map_apply]
  refine congrArg ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom) (Subtype.ext (funext fun p => ?_))
  obtain ⟨g₁, g₂⟩ := p
  show (back hcompat o).hom ((fwd' hcompat o).hom (c (e.symm (e g₁), e.symm (e g₂)))) = c (g₁, g₂)
  rw [e.symm_apply_apply, e.symm_apply_apply, back_hom_apply]
  obtain ⟨w, hw⟩ : ∃ w : (↥L)ˣ, Additive.ofMul w = c (g₁, g₂) := ⟨Additive.toMul (c (g₁, g₂)), rfl⟩
  rw [← hw]
  exact congrArg Additive.ofMul (backUnit_fwd hcompat o w _)

theorem map_fwd_injective [FiniteDimensional ℚ_[q] M] [Finite H] [FaithfulSMul H M] :
    Function.Injective (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat o) 2).hom := by
  classical
  have h90 := ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units q M H o.smul_algebraMap o.coe_smul_units (↥NL) NL.subtype
    Subtype.val_injective
  have hinj₀ := (groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 (Rep.ofMulDistribMulAction H (↥M)ˣ) NL h90).1
  have hinj : Function.Injective ((infNatTrans ℤ NL 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom := hinj₀
  intro x y hxy
  obtain ⟨cx, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π (Rep.ofMulDistribMulAction G (↥L)ˣ))).mp inferInstance x
  obtain ⟨cy, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π (Rep.ofMulDistribMulAction G (↥L)ˣ))).mp inferInstance y
  rw [map_fwd_eq_inf_map, map_fwd_eq_inf_map] at hxy
  have h2 := hinj hxy
  rw [← map_back_map_fwd' hcompat o cx, ← map_back_map_fwd' hcompat o cy, h2]

end ExtCitation.LocalLevel.Ws25IND
end

noncomputable section
namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_common_overlayer LocalLevel.eq_of_unramified_level_of_index_eq LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass Rw isZero_groupCohomology_one_res_units exists_common_overlayer eq_of_unramified_level_of_index_eq mem_of_unramified_level_of_forall_norm_smul_sub_lt_one exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace Ws25IND
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]

theorem cyclicLog_congr {Γ : Type} [Group Γ] {s s' : Γ} (h : s = s') (hs : ∀ g : Γ, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    (hs' : ∀ g : Γ, g ∈ Subgroup.zpowers s') (hfin' : IsOfFinOrder s') (g : Γ) :
    cyclicLog s hs hfin g = cyclicLog s' hs' hfin' g := by
  subst h; rfl

theorem pow_cyclicLog {Γ : Type} [Group Γ] (s : Γ) (hs : ∀ g : Γ, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (g : Γ) :
    s ^ cyclicLog s hs hfin g = g := by
  unfold cyclicLog
  have := (finEquivZPowers hfin).apply_symm_apply ⟨g, hs g⟩
  rw [finEquivZPowers_apply] at this
  exact congrArg Subtype.val this

theorem cyclicLog_lt {Γ : Type} [Group Γ] (s : Γ) (hs : ∀ g : Γ, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (g : Γ) :
    cyclicLog s hs hfin g < orderOf s :=
  ((finEquivZPowers hfin).symm ⟨g, hs g⟩).isLt

theorem cyclicLog_eq_of_pow_eq {Γ : Type} [Group Γ] (s : Γ) (hs : ∀ g : Γ, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {i : ℕ} (hi : i < orderOf s) {g : Γ} (h : s ^ i = g) : cyclicLog s hs hfin g = i := by
  apply pow_injOn_Iio_orderOf (x := s)
  · exact cyclicLog_lt s hs hfin g
  · exact hi
  · show s ^ cyclicLog s hs hfin g = s ^ i
    rw [pow_cyclicLog, h]

theorem gen_of_surj {Γ Δ : Type} [Group Γ] [Group Δ] (θ : Γ →* Δ) (hθ : Function.Surjective θ)
    (Ñ : Subgroup Γ) [Ñ.Normal] (hÑ : ∀ a, a ∈ Ñ ↔ θ a = 1)
    (φb : Δ) (hφ : ∀ g, g ∈ Subgroup.zpowers φb) (ψ₀ : Γ) (hψ₀ : θ ψ₀ = φb) :
    ∀ g : Γ ⧸ Ñ, g ∈ Subgroup.zpowers (QuotientGroup.mk' Ñ ψ₀) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hφ (θ a))
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [hÑ, map_mul, map_inv, map_zpow, hψ₀, hk, inv_mul_cancel]

theorem orderOf_mk_eq {Γ Δ : Type} [Group Γ] [Group Δ] (θ : Γ →* Δ)
    (Ñ : Subgroup Γ) [Ñ.Normal] (hÑ : ∀ a, a ∈ Ñ ↔ θ a = 1) (ψ₀ : Γ) :
    orderOf (QuotientGroup.mk' Ñ ψ₀) = orderOf (θ ψ₀) := by

  have hle : Ñ ≤ θ.ker := fun a ha => (hÑ a).mp ha
  set θb : Γ ⧸ Ñ →* Δ := QuotientGroup.lift Ñ θ hle with hθb
  have hinj : Function.Injective θb := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    induction z using QuotientGroup.induction_on with
    | H a =>
      rw [MonoidHom.mem_ker] at hz
      change θ a = 1 at hz
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
      exact (hÑ a).mpr hz
  rw [← orderOf_injective θb hinj (QuotientGroup.mk' Ñ ψ₀)]
  rfl

theorem cyclicLog_mk_eq {Γ Δ : Type} [Group Γ] [Group Δ] (θ : Γ →* Δ) (hθ : Function.Surjective θ)
    (Ñ : Subgroup Γ) [Ñ.Normal] (hÑ : ∀ a, a ∈ Ñ ↔ θ a = 1)
    (φb : Δ) (hφ : ∀ g, g ∈ Subgroup.zpowers φb) (hfin : IsOfFinOrder φb) (ψ₀ : Γ) (hψ₀ : θ ψ₀ = φb)
    (hψ : ∀ g : Γ ⧸ Ñ, g ∈ Subgroup.zpowers (QuotientGroup.mk' Ñ ψ₀)) (hfinψ : IsOfFinOrder (QuotientGroup.mk' Ñ ψ₀)) (a : Γ) :
    cyclicLog (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ (QuotientGroup.mk a) = cyclicLog φb hφ hfin (θ a) := by
  have hord : orderOf (QuotientGroup.mk' Ñ ψ₀) = orderOf φb := by rw [orderOf_mk_eq θ Ñ hÑ, hψ₀]
  apply cyclicLog_eq_of_pow_eq
  · rw [hord]; exact cyclicLog_lt _ _ _ _
  ·
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq, hÑ, map_mul, map_inv, map_pow, hψ₀, pow_cyclicLog, inv_mul_cancel]

section transport
variable {M : IntermediateField ℚ_[q] (PadicAlgCl q)} {H : Type} [Group H] [MulSemiringAction H M] [MulDistribMulAction H (↥M)ˣ]
variable {M'' : IntermediateField ℚ_[q] (PadicAlgCl q)} {hMM : M ≤ M''}
variable {H'' : Type} [Group H''] [MulSemiringAction H'' M''] [MulDistribMulAction H'' (↥M'')ˣ]
variable {P : Subgroup H''} [P.Normal] {ε : H ≃* H'' ⧸ P}
variable (hHcompat : ∀ (h : H) (u : (↥M)ˣ), ((h • u : (↥M)ˣ) : M) = h • (u : M))
variable (o₂ : OL M H M'' hMM H'' P ε)
variable (Nn : Subgroup H) [Nn.Normal]

abbrev θ : H'' →* H ⧸ Nn := (QuotientGroup.mk' Nn).comp (ε.symm.toMonoidHom.comp (QuotientGroup.mk' P))

omit hHcompat o₂ in
theorem θ_surjective : Function.Surjective (θ (ε := ε) Nn) :=
  (QuotientGroup.mk'_surjective Nn).comp (ε.symm.surjective.comp (QuotientGroup.mk'_surjective P))

include hHcompat o₂

theorem map_fwd_inf_carry (Ñ : Subgroup H'') [Ñ.Normal] (hÑ : ∀ a, a ∈ Ñ ↔ θ (ε := ε) Nn a = 1)
    (φ : H) (hφN : ∀ g : H ⧸ Nn, g ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ)) (hfin : IsOfFinOrder (QuotientGroup.mk' Nn φ))
    (πN : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)
    (hc : carryFun (QuotientGroup.mk' Nn φ) hφN hfin πN ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn))
    (ψ₀ : H'') (hψ₀ : θ (ε := ε) Nn ψ₀ = QuotientGroup.mk' Nn φ)
    (hψ : ∀ g : H'' ⧸ Ñ, g ∈ Subgroup.zpowers (QuotientGroup.mk' Ñ ψ₀)) (hfinψ : IsOfFinOrder (QuotientGroup.mk' Ñ ψ₀))
    (πÑ : (Rep.ofMulDistribMulAction H'' (↥M'')ˣ).quotientToInvariants Ñ)
    (hπÑ : (πÑ.1 : Additive (↥M'')ˣ) = (fwd hHcompat o₂).hom (πN.1 : Additive (↥M)ˣ))
    (hc' : carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ ∈ cocycles₂ ((Rep.ofMulDistribMulAction H'' (↥M'')ˣ).quotientToInvariants Ñ)) :
    (groupCohomology.map (ε.symm.toMonoidHom.comp (QuotientGroup.mk' P)) (fwd hHcompat o₂) 2).hom
        (((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
          ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom ⟨carryFun (QuotientGroup.mk' Nn φ) hφN hfin πN, hc⟩)) =
      ((infNatTrans ℤ Ñ 2).app (Rep.ofMulDistribMulAction H'' (↥M'')ˣ)).hom
        ((H2π ((Rep.ofMulDistribMulAction H'' (↥M'')ˣ).quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ, hc'⟩) := by
  change (groupCohomology.map (ε.symm.toMonoidHom.comp (QuotientGroup.mk' P)) (fwd hHcompat o₂) 2).hom
      ((groupCohomology.map (QuotientGroup.mk' Nn) (Rep.ofHom ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.quotientToInvariants_lift Nn)) 2).hom
        ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom ⟨carryFun (QuotientGroup.mk' Nn φ) hφN hfin πN, hc⟩)) =
    (groupCohomology.map (QuotientGroup.mk' Ñ) (Rep.ofHom ((Rep.ofMulDistribMulAction H'' (↥M'')ˣ).ρ.quotientToInvariants_lift Ñ)) 2).hom
      ((H2π ((Rep.ofMulDistribMulAction H'' (↥M'')ˣ).quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ, hc'⟩)
  rw [H2π_comp_map_apply, H2π_comp_map_apply]
  erw [H2π_comp_map_apply]
  refine congrArg ((H2π (Rep.ofMulDistribMulAction H'' (↥M'')ˣ)).hom) (Subtype.ext (funext fun p => ?_))
  obtain ⟨a, b⟩ := p
  show (fwd hHcompat o₂).hom ((carryFun (QuotientGroup.mk' Nn φ) hφN hfin πN (θ (ε := ε) Nn a, θ (ε := ε) Nn b)).1 : Additive (↥M)ˣ) =
    ((carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ (QuotientGroup.mk a, QuotientGroup.mk b)).1 : Additive (↥M'')ˣ)
  have hla := cyclicLog_mk_eq (θ (ε := ε) Nn) (θ_surjective Nn) Ñ hÑ _ hφN hfin ψ₀ hψ₀ hψ hfinψ a
  have hlb := cyclicLog_mk_eq (θ (ε := ε) Nn) (θ_surjective Nn) Ñ hÑ _ hφN hfin ψ₀ hψ₀ hψ hfinψ b
  have hord : orderOf (QuotientGroup.mk' Ñ ψ₀) = orderOf (QuotientGroup.mk' Nn φ) := by rw [orderOf_mk_eq (θ (ε := ε) Nn) Ñ hÑ, hψ₀]
  simp only [carryFun]
  rw [show (QuotientGroup.mk a : H'' ⧸ Ñ) = QuotientGroup.mk' Ñ a from rfl, show (QuotientGroup.mk b : H'' ⧸ Ñ) = QuotientGroup.mk' Ñ b from rfl] at *
  rw [hla, hlb, hord]
  split_ifs
  · exact hπÑ.symm
  · exact ((fwd hHcompat o₂).hom.toLinearMap.map_zero)

end transport

end ExtCitation.LocalLevel.Ws25IND
end

noncomputable section
namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_common_overlayer LocalLevel.eq_of_unramified_level_of_index_eq LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass Rw isZero_groupCohomology_one_res_units exists_common_overlayer eq_of_unramified_level_of_index_eq mem_of_unramified_level_of_forall_norm_smul_sub_lt_one exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace Ws25IND
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]

theorem OL.ofDatum {L : IntermediateField ℚ_[q] (PadicAlgCl q)} {G : Type} [Group G] [MulSemiringAction G L]
    {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
    {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}
    (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π) : OL L G M hLM H NL e :=
  ⟨d.smul_algebraMap, d.coe_smul_units, d.mem_layer_iff, d.coe_smul_eq⟩

section two_towers

variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
variable {G : Type} [Group G] [MulSemiringAction G L] [FaithfulSMul G L] [MulDistribMulAction G (↥L)ˣ]
variable (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))

variable {M : IntermediateField ℚ_[q] (PadicAlgCl q)} {hLM : L ≤ M}
variable {H : Type} [Group H] [MulSemiringAction H M] [MulDistribMulAction H (↥M)ˣ] {NL : Subgroup H} [NL.Normal] {e : G ≃* H ⧸ NL}
variable {M' : IntermediateField ℚ_[q] (PadicAlgCl q)} {hLM' : L ≤ M'}
variable {H' : Type} [Group H'] [MulSemiringAction H' M'] [MulDistribMulAction H' (↥M')ˣ] {NL' : Subgroup H'} [NL'.Normal] {e' : G ≃* H' ⧸ NL'}
variable (o : OL L G M hLM H NL e) (o' : OL L G M' hLM' H' NL' e')

variable {M'' : IntermediateField ℚ_[q] (PadicAlgCl q)} {hMM : M ≤ M''} {hMM' : M' ≤ M''}
variable {H'' : Type} [Group H''] [MulSemiringAction H'' M''] [MulDistribMulAction H'' (↥M'')ˣ]
variable {P P' : Subgroup H''} [P.Normal] [P'.Normal] {ε : H ≃* H'' ⧸ P} {ε' : H' ≃* H'' ⧸ P'}
variable (o₂ : OL M H M'' hMM H'' P ε) (o₂' : OL M' H' M'' hMM' H'' P' ε')

include hcompat o o' o₂ o₂'

theorem comp_eq (a : H'') :
    e.symm (QuotientGroup.mk (ε.symm (QuotientGroup.mk a : H'' ⧸ P)) : H ⧸ NL) =
      e'.symm (QuotientGroup.mk (ε'.symm (QuotientGroup.mk a : H'' ⧸ P')) : H' ⧸ NL') := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
  intro x
  apply Subtype.ext

  have h1 := o.coe_smul_eq (e.symm (QuotientGroup.mk (ε.symm (QuotientGroup.mk a : H'' ⧸ P)) : H ⧸ NL)) (ε.symm (QuotientGroup.mk a))
    (by rw [e.apply_symm_apply]) x
  have h2 := o₂.coe_smul_eq (ε.symm (QuotientGroup.mk a : H'' ⧸ P)) a (by rw [ε.apply_symm_apply]) ⟨(x : PadicAlgCl q), hLM x.2⟩
  have h1' := o'.coe_smul_eq (e'.symm (QuotientGroup.mk (ε'.symm (QuotientGroup.mk a : H'' ⧸ P')) : H' ⧸ NL')) (ε'.symm (QuotientGroup.mk a))
    (by rw [e'.apply_symm_apply]) x
  have h2' := o₂'.coe_smul_eq (ε'.symm (QuotientGroup.mk a : H'' ⧸ P')) a (by rw [ε'.apply_symm_apply]) ⟨(x : PadicAlgCl q), hLM' x.2⟩
  rw [h1, h2, h1', h2']

theorem map_map_fwd_eq (c : cocycles₂ (Rep.ofMulDistribMulAction G (↥L)ˣ)) :
    (groupCohomology.map (ε.symm.toMonoidHom.comp (QuotientGroup.mk' P)) (fwd o.coe_smul_units o₂) 2).hom
        ((groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat o) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c)) =
      (groupCohomology.map (ε'.symm.toMonoidHom.comp (QuotientGroup.mk' P')) (fwd o'.coe_smul_units o₂') 2).hom
        ((groupCohomology.map (e'.symm.toMonoidHom.comp (QuotientGroup.mk' NL')) (fwd hcompat o') 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c)) := by
  rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply]
  refine congrArg ((H2π (Rep.ofMulDistribMulAction H'' (↥M'')ˣ)).hom) (Subtype.ext (funext fun p => ?_))
  obtain ⟨a, b⟩ := p
  show (fwd o.coe_smul_units o₂).hom ((fwd hcompat o).hom (c (e.symm (QuotientGroup.mk (ε.symm (QuotientGroup.mk a : H'' ⧸ P)) : H ⧸ NL),
      e.symm (QuotientGroup.mk (ε.symm (QuotientGroup.mk b : H'' ⧸ P)) : H ⧸ NL)))) =
    (fwd o'.coe_smul_units o₂').hom ((fwd hcompat o').hom (c (e'.symm (QuotientGroup.mk (ε'.symm (QuotientGroup.mk a : H'' ⧸ P')) : H' ⧸ NL'),
      e'.symm (QuotientGroup.mk (ε'.symm (QuotientGroup.mk b : H'' ⧸ P')) : H' ⧸ NL'))))
  rw [← comp_eq hcompat o o' o₂ o₂' a, ← comp_eq hcompat o o' o₂ o₂' b]

  set w : (↥L)ˣ := Additive.toMul (c (e.symm (QuotientGroup.mk (ε.symm (QuotientGroup.mk a : H'' ⧸ P)) : H ⧸ NL),
      e.symm (QuotientGroup.mk (ε.symm (QuotientGroup.mk b : H'' ⧸ P)) : H ⧸ NL))) with hw
  have hc : c (e.symm (QuotientGroup.mk (ε.symm (QuotientGroup.mk a : H'' ⧸ P)) : H ⧸ NL),
      e.symm (QuotientGroup.mk (ε.symm (QuotientGroup.mk b : H'' ⧸ P)) : H ⧸ NL)) = Additive.ofMul w := rfl
  rw [hc]
  show Additive.ofMul (fwdUnit (hLM := hMM) (fwdUnit (hLM := hLM) w)) = Additive.ofMul (fwdUnit (hLM := hMM') (fwdUnit (hLM := hLM') w))
  first | rfl | exact congrArg Additive.ofMul (Units.ext (Subtype.ext rfl))

end two_towers

end ExtCitation.LocalLevel.Ws25IND
end

noncomputable section
namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_common_overlayer LocalLevel.eq_of_unramified_level_of_index_eq LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass Rw isZero_groupCohomology_one_res_units exists_common_overlayer eq_of_unramified_level_of_index_eq mem_of_unramified_level_of_forall_norm_smul_sub_lt_one exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace Ws25IND
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]

theorem norm_smul_eq (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) (x : L) :
    ‖((g • x : L) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖ := by
  haveI : Normal ℚ_[q] (PadicAlgCl q) := IsAlgClosure.normal ℚ_[q] (PadicAlgCl q)
  let σ : L ≃ₐ[ℚ_[q]] L := { MulSemiringAction.toRingEquiv G L g with commutes' := fun y => hG g y }
  let τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q := σ.liftNormal (PadicAlgCl q)
  have hcomm : τ (algebraMap L (PadicAlgCl q) x) = algebraMap L (PadicAlgCl q) (σ x) := AlgEquiv.liftNormal_commutes σ (PadicAlgCl q) x
  have h1 : ((g • x : L) : PadicAlgCl q) = τ (x : PadicAlgCl q) := hcomm.symm
  rw [h1]
  have := nnnorm_padicAlgCl_algEquiv q τ (x : PadicAlgCl q)
  exact congrArg (fun r : NNReal => (r : ℝ)) this

section level

variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)} {G : Type} [Group G] [MulSemiringAction G L]
variable {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
variable {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
variable {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
variable {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}
variable (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π)
variable {M'' : IntermediateField ℚ_[q] (PadicAlgCl q)} {hMM : M ≤ M''}
variable {H'' : Type} [Group H''] [MulSemiringAction H'' M''] [MulDistribMulAction H'' (↥M'')ˣ]
variable {P : Subgroup H''} [P.Normal] {ε : H ≃* H'' ⧸ P}
variable (o₂ : OL M H M'' hMM H'' P ε)
variable (hK'' : ∀ x : M'', (x : PadicAlgCl q) ∈ K ↔ ∀ h : H'', h • x = x)
include d o₂ hK''

theorem smul_fwdUnit_pi (h : H'') : h • fwdUnit (hLM := hMM) π = fwdUnit (hLM := hMM) π := by
  apply Units.ext
  rw [o₂.coe_smul_units]
  exact (hK'' _).mp d.pi_mem h

theorem exists_of_fixed (Ñ : Subgroup H'') (hÑ : ∀ a, a ∈ Ñ ↔ θ (ε := ε) Nn a = 1)
    (y : M'') (hy : ∀ n ∈ Ñ, n • y = y) :
    ∃ y₀ : M, ((y₀ : M) : PadicAlgCl q) = (y : PadicAlgCl q) ∧ ∀ n ∈ Nn, n • y₀ = y₀ := by

  have hyM : (y : PadicAlgCl q) ∈ M := by
    rw [o₂.mem_layer_iff]
    intro a ha
    apply hy
    rw [hÑ]
    show QuotientGroup.mk' Nn (ε.symm (QuotientGroup.mk' P a)) = 1
    have hPa : QuotientGroup.mk' P a = 1 := by rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff a).mpr ha
    rw [hPa, map_one, map_one]
  refine ⟨⟨(y : PadicAlgCl q), hyM⟩, rfl, ?_⟩
  intro n hn
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ε n)
  have haÑ : a ∈ Ñ := by
    rw [hÑ]
    show QuotientGroup.mk' Nn (ε.symm (QuotientGroup.mk' P a)) = 1
    have hPa : QuotientGroup.mk' P a = ε n := by rw [QuotientGroup.mk'_apply]; exact ha
    rw [hPa, ε.symm_apply_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff n).mpr hn
  apply Subtype.ext
  have := o₂.coe_smul_eq n a ha ⟨(y : PadicAlgCl q), hyM⟩
  rw [this]
  have hy' := hy a haÑ
  have : (⟨((⟨(y : PadicAlgCl q), hyM⟩ : M) : PadicAlgCl q), hMM hyM⟩ : M'') = y := Subtype.ext rfl
  rw [this, hy']

theorem norm_le_of_fixed (Ñ : Subgroup H'') (hÑ : ∀ a, a ∈ Ñ ↔ θ (ε := ε) Nn a = 1)
    (y : M'') (hy : ∀ n ∈ Ñ, n • y = y) (hy1 : ‖(y : PadicAlgCl q)‖ < 1) :
    ‖(y : PadicAlgCl q)‖ ≤ ‖(((fwdUnit (hLM := hMM) π : (↥M'')ˣ) : M'') : PadicAlgCl q)‖ := by
  obtain ⟨y₀, hy₀, hy₀N⟩ := exists_of_fixed d o₂ hK'' Ñ hÑ y hy
  rw [← hy₀] at hy1 ⊢
  exact d.norm_le_norm_pi y₀ hy₀N hy1

theorem frobenius_lift (Ñ : Subgroup H'') (hÑ : ∀ a, a ∈ Ñ ↔ θ (ε := ε) Nn a = 1)
    (ψ₀ : H'') (hψ₀ : θ (ε := ε) Nn ψ₀ = QuotientGroup.mk' Nn φ)
    (x : M'') (hx : ∀ n ∈ Ñ, n • x = x) (hx1 : ‖(x : PadicAlgCl q)‖ ≤ 1) :
    ‖((ψ₀ • x : M'') : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1 := by
  obtain ⟨x₀, hx₀, hx₀N⟩ := exists_of_fixed d o₂ hK'' Ñ hÑ x hx

  have h1 := o₂.coe_smul_eq (ε.symm (QuotientGroup.mk ψ₀ : H'' ⧸ P)) ψ₀ (by rw [ε.apply_symm_apply]) x₀
  have hxx : (⟨((x₀ : M) : PadicAlgCl q), hMM x₀.2⟩ : M'') = x := Subtype.ext hx₀
  rw [hxx] at h1
  have hmem : φ⁻¹ * ε.symm (QuotientGroup.mk ψ₀ : H'' ⧸ P) ∈ Nn := by
    rw [← QuotientGroup.eq]
    exact hψ₀.symm
  have h2 : ε.symm (QuotientGroup.mk ψ₀ : H'' ⧸ P) • x₀ = φ • x₀ := by
    conv_lhs => rw [show ε.symm (QuotientGroup.mk ψ₀ : H'' ⧸ P) = φ * (φ⁻¹ * ε.symm (QuotientGroup.mk ψ₀ : H'' ⧸ P)) by group]
    rw [mul_smul, hx₀N _ hmem]
  rw [← h1, h2, ← hx₀]
  exact d.frobenius x₀ hx₀N (by rw [hx₀]; exact hx1)

end level

end ExtCitation.LocalLevel.Ws25IND
end

noncomputable section
namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_common_overlayer LocalLevel.eq_of_unramified_level_of_index_eq LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass Rw isZero_groupCohomology_one_res_units exists_common_overlayer eq_of_unramified_level_of_index_eq mem_of_unramified_level_of_forall_norm_smul_sub_lt_one exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun"
namespace Ws25IND
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]

theorem map_eq_map_fwd {L : IntermediateField ℚ_[q] (PadicAlgCl q)} {G : Type} [Group G] [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} {hLM : L ≤ M}
    {H : Type} [Group H] [MulSemiringAction H M] [MulDistribMulAction H (↥M)ˣ] {NL : Subgroup H} [NL.Normal] {e : G ≃* H ⧸ NL}
    (o : OL L G M hLM H NL e)
    (ι : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction H (↥M)ˣ)
    (hι : ∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q))
    (c : cocycles₂ (Rep.ofMulDistribMulAction G (↥L)ˣ)) :
    (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c) =
      (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (fwd hcompat o) 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom c) := by
  rw [H2π_comp_map_apply, H2π_comp_map_apply]
  refine congrArg ((H2π (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom) (Subtype.ext (funext fun p => ?_))
  obtain ⟨a, b⟩ := p
  exact eq_fwd hcompat o ι hι (Additive.toMul (c (Prod.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL))
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (a, b))))

theorem carryFun_congr {Γ : Type} [Group Γ] {s s' : Γ} (h : s = s') (hs : ∀ g : Γ, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    (hs' : ∀ g : Γ, g ∈ Subgroup.zpowers s') (hfin' : IsOfFinOrder s') {A : Rep ℤ Γ} (a : A) :
    carryFun s hs hfin a = carryFun s' hs' hfin' a := by
  subst h; rfl

end ExtCitation.LocalLevel.Ws25IND
end

open ExtCitation.LocalLevel.Ws25IND in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K)
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
    {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}
    (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ))
    (hu : ∀ (ι : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction H (↥M)ˣ),
      (∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q)) →
      ∀ (hfin : IsOfFinOrder (QuotientGroup.mk' Nn φ))
        (hc : carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)),
        (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι 2).hom u =
          ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
            ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
              ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩)) :
    IsLocalFundamentalClass q L G K u := by
  classical
  intro M' _ hLM' H' _ _ _ _ _ NL' Nn' _ _ e' φ' π' d' ι' hι' hfin' hc'

  obtain ⟨cu, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π (Rep.ofMulDistribMulAction G (↥L)ˣ))).mp inferInstance u
  have o : OL L G M hLM H NL e := OL.ofDatum d
  have o' : OL L G M' hLM' H' NL' e' := OL.ofDatum d'
  rw [map_eq_map_fwd hcompat o' ι' hι']

  have hfin₀ : IsOfFinOrder (QuotientGroup.mk' Nn φ) := isOfFinOrder_of_finite _
  have hc₀ : carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin₀ d.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn) := by
    refine groupCohomology.carryFun_mem_cocycles2 _ _ _ _ (Subtype.ext ?_)
    exact congrArg Additive.ofMul (d.smul_pi φ)
  have hpin := hu (fwd hcompat o) (fwd_char hcompat o) hfin₀ hc₀

  obtain ⟨M'', _, hMM, hMM', H'', _, _, _, _, _, P, P', _, _, ε, ε', h1, h2, h3, h4, h5, h6, h7⟩ :=
    ExtCitation.LocalLevel.exists_common_overlayer q K M H d.smul_algebraMap d.coe_smul_units (hK.le.trans hLM) d.mem_base_iff
      M' H' d'.smul_algebraMap d'.coe_smul_units (hK.le.trans hLM') d'.mem_base_iff
  have o₂ : OL M H M'' hMM H'' P ε := ⟨h1, h2, h4, h6⟩
  have o₂' : OL M' H' M'' hMM' H'' P' ε' := ⟨h1, h2, h5, h7⟩

  apply map_fwd_injective d'.coe_smul_units o₂'
  rw [← map_map_fwd_eq hcompat o o' o₂ o₂' cu, hpin]

  set Ñ : Subgroup H'' := (θ (ε := ε) Nn).ker with hÑdef
  have hÑ : ∀ a, a ∈ Ñ ↔ θ (ε := ε) Nn a = 1 := fun a => MonoidHom.mem_ker
  set Ñ' : Subgroup H'' := (θ (ε := ε') Nn').ker with hÑ'def
  have hÑ' : ∀ a, a ∈ Ñ' ↔ θ (ε := ε') Nn' a = 1 := fun a => MonoidHom.mem_ker

  have hidxÑ : Ñ.index = Nat.card G := by
    rw [hÑdef, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (θ_surjective (ε := ε) Nn), Subgroup.card_top, d.card_quotient]
  have hidxÑ' : Ñ'.index = Nat.card G := by
    rw [hÑ'def, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (θ_surjective (ε := ε') Nn'), Subgroup.card_top, d'.card_quotient]

  have hπfix : ∀ h : H'', h • fwdUnit (hLM := hMM) π = fwdUnit (hLM := hMM) π := smul_fwdUnit_pi d o₂ h3
  have hπ'fix : ∀ h : H'', h • fwdUnit (hLM := hMM') π' = fwdUnit (hLM := hMM') π' := smul_fwdUnit_pi d' o₂' h3
  have hπfixL : ∀ h : H'', h • ((fwdUnit (hLM := hMM) π : (↥M'')ˣ) : M'') = ((fwdUnit (hLM := hMM) π : (↥M'')ˣ) : M'') := fun h => by
    rw [← h2, hπfix]
  have hπ'fixL : ∀ h : H'', h • ((fwdUnit (hLM := hMM') π' : (↥M'')ˣ) : M'') = ((fwdUnit (hLM := hMM') π' : (↥M'')ˣ) : M'') := fun h => by
    rw [← h2, hπ'fix]

  have hNN : Ñ = Ñ' :=
    ExtCitation.LocalLevel.eq_of_unramified_level_of_index_eq q M'' H'' h1 Ñ Ñ' (hidxÑ.trans hidxÑ'.symm)
      _ hπfixL d.norm_pi_lt (norm_le_of_fixed d o₂ h3 Ñ hÑ) _ hπ'fixL d'.norm_pi_lt (norm_le_of_fixed d' o₂' h3 Ñ' hÑ')
  have hÑ'' : ∀ a, a ∈ Ñ ↔ θ (ε := ε') Nn' a = 1 := fun a => by rw [hNN]; exact hÑ' a

  obtain ⟨ψ₀, hψ₀⟩ := θ_surjective (ε := ε) Nn (QuotientGroup.mk' Nn φ)
  obtain ⟨ψ₀', hψ₀'⟩ := θ_surjective (ε := ε') Nn' (QuotientGroup.mk' Nn' φ')
  have hψ : ∀ g : H'' ⧸ Ñ, g ∈ Subgroup.zpowers (QuotientGroup.mk' Ñ ψ₀) := gen_of_surj _ (θ_surjective Nn) Ñ hÑ _ d.mem_zpowers ψ₀ hψ₀
  have hψ' : ∀ g : H'' ⧸ Ñ, g ∈ Subgroup.zpowers (QuotientGroup.mk' Ñ ψ₀') := gen_of_surj _ (θ_surjective Nn') Ñ hÑ'' _ d'.mem_zpowers ψ₀' hψ₀'
  have hfinψ : IsOfFinOrder (QuotientGroup.mk' Ñ ψ₀) := isOfFinOrder_of_finite _
  have hfinψ' : IsOfFinOrder (QuotientGroup.mk' Ñ ψ₀') := isOfFinOrder_of_finite _

  set A'' := Rep.ofMulDistribMulAction H'' (↥M'')ˣ with hA''
  have hmemπ : (Additive.ofMul (fwdUnit (hLM := hMM) π) : A'') ∈ Representation.invariants (A''.ρ.comp Ñ.subtype) :=
    fun n => congrArg Additive.ofMul (hπfix (n : H''))
  have hmemπ' : (Additive.ofMul (fwdUnit (hLM := hMM') π') : A'') ∈ Representation.invariants (A''.ρ.comp Ñ.subtype) :=
    fun n => congrArg Additive.ofMul (hπ'fix (n : H''))
  set πÑ : A''.quotientToInvariants Ñ := ⟨_, hmemπ⟩ with hπÑ
  set πÑ' : A''.quotientToInvariants Ñ := ⟨_, hmemπ'⟩ with hπÑ'
  have hcπ : carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ ∈ cocycles₂ (A''.quotientToInvariants Ñ) :=
    groupCohomology.carryFun_mem_cocycles2 _ _ _ _ (Subtype.ext (congrArg Additive.ofMul (hπfix ψ₀)))
  have hcπ' : carryFun (QuotientGroup.mk' Ñ ψ₀') hψ' hfinψ' πÑ' ∈ cocycles₂ (A''.quotientToInvariants Ñ) :=
    groupCohomology.carryFun_mem_cocycles2 _ _ _ _ (Subtype.ext (congrArg Additive.ofMul (hπ'fix ψ₀')))

  rw [map_fwd_inf_carry d.coe_smul_units o₂ Nn Ñ hÑ φ d.mem_zpowers hfin₀ d.piInv hc₀ ψ₀ hψ₀ hψ hfinψ πÑ rfl hcπ,
    map_fwd_inf_carry d'.coe_smul_units o₂' Nn' Ñ hÑ'' φ' d'.mem_zpowers hfin' d'.piInv hc' ψ₀' hψ₀' hψ' hfinψ' πÑ' rfl hcπ']
  congr 1

  have hmemg : ψ₀⁻¹ * ψ₀' ∈ Ñ := by
    refine ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one q M'' H'' h1 Ñ _ hπfixL d.norm_pi_lt
      (norm_le_of_fixed d o₂ h3 Ñ hÑ) (ψ₀⁻¹ * ψ₀') ?_
    intro x hx hx1
    have f1 := frobenius_lift d o₂ h3 Ñ hÑ ψ₀ hψ₀ x hx hx1
    have f2 := frobenius_lift d' o₂' h3 Ñ hÑ'' ψ₀' hψ₀' x hx hx1
    have hxx : ((((ψ₀⁻¹ * ψ₀') • x : M'') : PadicAlgCl q)) - (x : PadicAlgCl q) =
        (((ψ₀⁻¹ • (ψ₀' • x - ψ₀ • x) : M'') : PadicAlgCl q)) := by
      rw [smul_sub, mul_smul, inv_smul_smul]; rfl
    rw [hxx, norm_smul_eq M'' H'' h1]
    have : (((ψ₀' • x - ψ₀ • x : M'') : PadicAlgCl q)) =
        ((((ψ₀' • x : M'') : PadicAlgCl q)) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))) +
          ((x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K)) - ((ψ₀ • x : M'') : PadicAlgCl q)) := by
      push_cast; ring
    rw [this]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt f2 ?_)
    rwa [norm_sub_rev]
  have hgen : QuotientGroup.mk' Ñ ψ₀' = QuotientGroup.mk' Ñ ψ₀ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    exact hmemg
  have hswap : carryFun (QuotientGroup.mk' Ñ ψ₀') hψ' hfinψ' πÑ' = carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ' :=
    carryFun_congr hgen _ _ _ _ _

  have hnorm : ‖(((fwdUnit (hLM := hMM) π : (↥M'')ˣ) : M'') : PadicAlgCl q)‖ = ‖(((fwdUnit (hLM := hMM') π' : (↥M'')ˣ) : M'') : PadicAlgCl q)‖ :=
    le_antisymm (norm_le_of_fixed d' o₂' h3 Ñ hÑ'' _ (fun n _ => hπfixL n) d.norm_pi_lt)
      (norm_le_of_fixed d o₂ h3 Ñ hÑ _ (fun n _ => hπ'fixL n) d'.norm_pi_lt)

  obtain ⟨inv, hinv⟩ := ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun q M'' H'' h1 h2 Ñ ψ₀ hψ hfinψ
    (fwdUnit (hLM := hMM) π) hπfix d.norm_pi_lt (norm_le_of_fixed d o₂ h3 Ñ hÑ)
  set wÑ : A''.quotientToInvariants Ñ := πÑ' - πÑ with hwÑ
  have hcw : carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ wÑ ∈ cocycles₂ (A''.quotientToInvariants Ñ) := by
    refine groupCohomology.carryFun_mem_cocycles2 _ _ _ _ ?_
    rw [hwÑ, map_sub]
    congr 1
    · exact Subtype.ext (congrArg Additive.ofMul (hπ'fix ψ₀))
    · exact Subtype.ext (congrArg Additive.ofMul (hπfix ψ₀))
  have hcπ'ψ : carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ' ∈ cocycles₂ (A''.quotientToInvariants Ñ) := hswap ▸ hcπ'
  have hw0 : (H2π (A''.quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ wÑ, hcw⟩ = 0 := by
    have hne : ‖(((fwdUnit (hLM := hMM) π : (↥M'')ˣ) : M'') : PadicAlgCl q)‖ ≠ 0 :=
      ne_of_gt (norm_pos_iff.mpr (fun h0 => (fwdUnit (hLM := hMM) π).ne_zero (Subtype.ext h0)))
    have hval := hinv wÑ 0 hcw (by
      rw [zpow_zero]
      show ‖((((fwdUnit (hLM := hMM') π' * (fwdUnit (hLM := hMM) π)⁻¹ : (↥M'')ˣ)) : M'') : PadicAlgCl q)‖ = 1
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      push_cast
      rw [norm_mul, norm_inv, hnorm, ← hnorm, mul_inv_cancel₀ hne])
    rw [Int.cast_zero] at hval
    exact (map_eq_zero_iff inv inv.injective).mp hval

  have hsum : πÑ' = πÑ + wÑ := by rw [hwÑ]; abel
  symm
  calc (H2π (A''.quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀') hψ' hfinψ' πÑ', hcπ'⟩
      = (H2π (A''.quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ', hcπ'ψ⟩ := by
        congr 1; exact Subtype.ext hswap
    _ = (H2π (A''.quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ (πÑ + wÑ), hsum ▸ hcπ'ψ⟩ := by
        congr 1; exact Subtype.ext (congrArg (carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ) hsum)
    _ = (H2π (A''.quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ, hcπ⟩ +
          (H2π (A''.quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ wÑ, hcw⟩ :=
        groupCohomology.carry_H2pi_add _ hψ hfinψ πÑ wÑ hcπ hcw _
    _ = (H2π (A''.quotientToInvariants Ñ)).hom ⟨carryFun (QuotientGroup.mk' Ñ ψ₀) hψ hfinψ πÑ, hcπ⟩ := by rw [hw0, add_zero]

end S_ExtCitation_LocalLevel_isLocalFundamentalClass_of_pin
end P2MW
export P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_of_pin (solution)
