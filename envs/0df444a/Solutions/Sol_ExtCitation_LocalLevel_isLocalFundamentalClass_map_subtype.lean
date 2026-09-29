-- Prove2me | solution 1 for ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/58d1ec5a-93b3-5adc-9f4a-d27dadffd71a

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
import Theorems.Thm_ExtCitation_LocalLevel_isLocalFundamentalClass_of_pin
import Theorems.Thm_ExtCitation_LocalLevel_exists_overlayer_unramified_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.ExtCitation.LocalLevel"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_frobenius_uniformiser_inf_level LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun LocalLevel.isLocalFundamentalClass_of_pin LocalLevel.exists_overlayer_unramified_level"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass Rw exists_frobenius_uniformiser_inf_level exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun isLocalFundamentalClass_of_pin exists_overlayer_unramified_level"
namespace ResFC
p2m_open "ExtCitation.LocalLevel ExtCitation"

section SubDatumGroup
variable {G H : Type} [Group G] [Group H] (S : Subgroup G) (NL : Subgroup H) [NL.Normal] (e : G ≃* H ⧸ NL)

def proj : H →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)

theorem proj_apply (h : H) : proj NL e h = e.symm (QuotientGroup.mk h) := rfl

theorem proj_surjective : Function.Surjective (proj NL e) := fun g => by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e g)
  exact ⟨h, by rw [proj_apply, hh, MulEquiv.symm_apply_apply]⟩

theorem proj_eq_iff (h : H) (g : G) : proj NL e h = g ↔ (QuotientGroup.mk h : H ⧸ NL) = e g := by
  rw [proj_apply, MulEquiv.symm_apply_eq]

theorem proj_eq_one_iff (h : H) : proj NL e h = 1 ↔ h ∈ NL := by
  rw [proj_eq_iff, map_one, QuotientGroup.eq_one_iff]

def HS : Subgroup H := S.comap (proj NL e)

theorem mem_HS (h : H) : h ∈ HS S NL e ↔ proj NL e h ∈ S := Iff.rfl

theorem NL_le_HS : NL ≤ HS S NL e := fun h hh => by
  rw [mem_HS, (proj_eq_one_iff NL e h).2 hh]; exact S.one_mem

def projS : ↥(HS S NL e) →* ↥S :=
  ((proj NL e).comp (HS S NL e).subtype).codRestrict S (fun h => h.2)

theorem coe_projS (h : ↥(HS S NL e)) : ((projS S NL e h : ↥S) : G) = proj NL e (h : H) := rfl

theorem projS_surjective : Function.Surjective (projS S NL e) := fun s => by
  obtain ⟨h, hh⟩ := proj_surjective NL e (s : G)
  refine ⟨⟨h, by rw [mem_HS, hh]; exact s.2⟩, Subtype.ext ?_⟩
  rw [coe_projS]; exact hh

theorem ker_projS : (projS S NL e).ker = NL.subgroupOf (HS S NL e) := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← proj_eq_one_iff NL e, ← coe_projS S NL e h]
  exact ⟨fun h1 => by rw [h1]; rfl, fun h1 => Subtype.ext h1⟩

noncomputable def eS : ↥S ≃* ↥(HS S NL e) ⧸ NL.subgroupOf (HS S NL e) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_projS S NL e)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective (projS S NL e) (projS_surjective S NL e))).symm

theorem eS_projS (h : ↥(HS S NL e)) :
    eS S NL e (projS S NL e h) = QuotientGroup.mk h := by
  rw [eS, MulEquiv.symm_apply_eq]
  rfl

theorem mk_eq_eS_iff (h : ↥(HS S NL e)) (s : ↥S) :
    (QuotientGroup.mk h : ↥(HS S NL e) ⧸ NL.subgroupOf (HS S NL e)) = eS S NL e s ↔ projS S NL e h = s := by
  rw [← eS_projS, (eS S NL e).apply_eq_iff_eq]

theorem orderOf_mk_subgroupOf {K N : Subgroup H} [N.Normal] (x : ↥K) :
    orderOf (QuotientGroup.mk' (N.subgroupOf K) x) = orderOf (QuotientGroup.mk' N (x : H)) := by
  let f : ↥K ⧸ N.subgroupOf K →* H ⧸ N :=
    QuotientGroup.lift (N.subgroupOf K) ((QuotientGroup.mk' N).comp K.subtype) (fun y hy => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact (QuotientGroup.eq_one_iff _).1 hc
  rw [← orderOf_injective f hf]
  rfl

section Unram
variable (Nn : Subgroup H) [Nn.Normal] (ψ : ↥(HS S NL e)) (k : ℕ)

def NnS : Subgroup ↥(HS S NL e) :=
  (Subgroup.zpowers ((QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) ^ k)).comap
    (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)))

theorem subgroupOf_le_NnS : Nn.subgroupOf (HS S NL e) ≤ NnS S NL e Nn ψ k := fun n hn => by
  rw [NnS, Subgroup.mem_comap]
  have : QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
  rw [this]
  exact Subgroup.one_mem _

theorem normal_NnS (hψ : ∀ c : ↥(HS S NL e) ⧸ Nn.subgroupOf (HS S NL e),
    c ∈ Subgroup.zpowers (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ)) : (NnS S NL e Nn ψ k).Normal := by
  haveI : (Subgroup.zpowers ((QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) ^ k)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hψ g)
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ ^ a)
        ((QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ ^ k) ^ b) := by
      rw [← zpow_natCast, ← zpow_mul]
      exact Commute.zpow_zpow (Commute.refl _) a _
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) b
  exact Subgroup.Normal.comap inferInstance _

theorem index_NnS (htfin : IsOfFinOrder (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ))
    (hψ : ∀ c : ↥(HS S NL e) ⧸ Nn.subgroupOf (HS S NL e), c ∈ Subgroup.zpowers (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ))
    (hk : k ≠ 0) (hkd : k ∣ orderOf (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ)) :
    (NnS S NL e Nn ψ k).index = k := by
  set t := QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ with ht
  have hidx : (NnS S NL e Nn ψ k).index = (Subgroup.zpowers (t ^ k)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [hidx]
  have htop : Subgroup.zpowers t = ⊤ := by rw [eq_top_iff]; intro c _; exact hψ c
  have hcard : Nat.card (↥(HS S NL e) ⧸ Nn.subgroupOf (HS S NL e)) = orderOf t := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top]
  have h1 := Subgroup.card_mul_index (Subgroup.zpowers (t ^ k))
  rw [Nat.card_zpowers, orderOf_pow_of_dvd hk hkd, hcard] at h1
  have hpos : 0 < orderOf t := htfin.orderOf_pos
  obtain ⟨m, hm⟩ := hkd
  rw [hm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)] at h1
  rw [hm] at hpos
  have : m * (Subgroup.zpowers (t ^ k)).index = m * k := by
    have h2 : m * (Subgroup.zpowers (t ^ k)).index = k * m := h1
    rw [h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mul_pos_left hpos) this

theorem mem_zpowers_NnS
    (hψ : ∀ c : ↥(HS S NL e) ⧸ Nn.subgroupOf (HS S NL e), c ∈ Subgroup.zpowers (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ))
    [hN : (NnS S NL e Nn ψ k).Normal] (c : ↥(HS S NL e) ⧸ NnS S NL e Nn ψ k) :
    c ∈ Subgroup.zpowers (QuotientGroup.mk' (NnS S NL e Nn ψ k) ψ) := by
  induction c using QuotientGroup.induction_on with
  | H h =>
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hψ (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) h))
    rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hi
    refine ⟨i, ?_⟩
    change (QuotientGroup.mk' (NnS S NL e Nn ψ k) ψ) ^ i = QuotientGroup.mk h
    rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact subgroupOf_le_NnS S NL e Nn ψ k hi

end Unram

end SubDatumGroup

section SubDatum
variable (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    [MulDistribMulAction G (↥L)ˣ]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K)
    (S : Subgroup G) (KS : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] KS] (hKS : IsBase q L (↥S) KS)
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
    {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}
    (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π)

scoped instance faithfulSMul_subgroup (T : Subgroup H) : FaithfulSMul (↥T) M :=
  ⟨fun {a b} h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := H) (α := ↥M) h)⟩

include d hKS in

theorem mem_KS_iff (x : M) : (x : PadicAlgCl q) ∈ KS ↔ ∀ h ∈ HS S NL e, h • x = x := by
  constructor
  · intro hx h hh
    have hxL : (x : PadicAlgCl q) ∈ L := hKS.le hx
    have key := d.coe_smul_eq (proj NL e h) h ((proj_eq_iff NL e h _).1 rfl) ⟨x, hxL⟩
    have hfix := (hKS.mem_iff ⟨(x : PadicAlgCl q), hxL⟩).1 hx ⟨proj NL e h, hh⟩
    apply Subtype.ext
    change ((h • x : M) : PadicAlgCl q) = x
    have : (⟨((⟨(x : PadicAlgCl q), hxL⟩ : L) : PadicAlgCl q), hLM hxL⟩ : M) = x := Subtype.ext rfl
    rw [this] at key
    rw [← key]
    exact congrArg (fun y : L => (y : PadicAlgCl q)) hfix
  · intro hx
    have hxL : (x : PadicAlgCl q) ∈ L := (d.mem_layer_iff x).2 (fun h hh => hx h (NL_le_HS S NL e hh))
    apply (hKS.mem_iff ⟨(x : PadicAlgCl q), hxL⟩).2
    intro s
    obtain ⟨h, hh⟩ := projS_surjective S NL e s
    have key := d.coe_smul_eq (s : G) h ((proj_eq_iff NL e h _).1 (by rw [← hh]; rfl)) ⟨x, hxL⟩
    apply Subtype.ext
    change (((s • (⟨(x : PadicAlgCl q), hxL⟩ : L)) : L) : PadicAlgCl q) = x
    have : (⟨((⟨(x : PadicAlgCl q), hxL⟩ : L) : PadicAlgCl q), hLM hxL⟩ : M) = x := Subtype.ext rfl
    rw [this] at key
    exact key.trans (congrArg (fun y : M => (y : PadicAlgCl q)) (hx h h.2))

include d hKS in

theorem subDatum (ψ : ↥(HS S NL e)) (π' : (↥M)ˣ)
    (hgen : ∀ c : ↥(HS S NL e) ⧸ Nn.subgroupOf (HS S NL e), c ∈ Subgroup.zpowers (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ))
    (hfrobψ : ∀ x : M, (∀ n ∈ Nn ⊓ HS S NL e, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((((ψ : H) • x : M)) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q KS))‖ < 1)
    (hπ'S : ∀ s ∈ HS S NL e, s • π' = π') (hπ'1 : ‖((π' : M) : PadicAlgCl q)‖ < 1)
    (hπ'max : ∀ y : M, (∀ n ∈ Nn ⊓ HS S NL e, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π' : M) : PadicAlgCl q)‖)
    [(NnS S NL e Nn ψ (Nat.card S)).Normal] (hidx : (NnS S NL e Nn ψ (Nat.card S)).index = Nat.card S) :
    IsUnramOverlayerDatum q L (↥S) KS M hLM (↥(HS S NL e)) (NL.subgroupOf (HS S NL e)) (NnS S NL e Nn ψ (Nat.card S))
      (eS S NL e) ψ π' where
  smul_algebraMap h x := d.smul_algebraMap h x
  coe_smul_units h u := d.coe_smul_units h u
  mem_base_iff x := by
    rw [mem_KS_iff q L G K S KS hKS d]
    exact ⟨fun h1 h => h1 h h.2, fun h1 h hh => h1 ⟨h, hh⟩⟩
  mem_layer_iff x := by
    rw [d.mem_layer_iff]
    constructor
    · intro h1 h hh; exact h1 h hh
    · intro h1 h hh; exact h1 ⟨h, NL_le_HS S NL e hh⟩ hh
  coe_smul_eq g h hgh x := by
    rw [mk_eq_eS_iff] at hgh
    have h1 : proj NL e (h : H) = (g : G) := by rw [← coe_projS, hgh]
    exact d.coe_smul_eq (g : G) h ((proj_eq_iff NL e h _).1 h1) x
  card_quotient := hidx
  mem_zpowers := mem_zpowers_NnS S NL e Nn ψ (Nat.card S) hgen
  frobenius x hx hx1 := hfrobψ x (fun n hn => hx ⟨n, hn.2⟩ (subgroupOf_le_NnS S NL e Nn ψ _ (by exact hn.1))) hx1
  smul_pi h := hπ'S h h.2
  pi_mem := (mem_KS_iff q L G K S KS hKS d (π' : M)).2 (fun h hh => by rw [← d.coe_smul_units, hπ'S h hh])
  norm_pi_lt := hπ'1
  norm_le_norm_pi y hy hy1 := hπ'max y (fun n hn => hy ⟨n, hn.2⟩ (subgroupOf_le_NnS S NL e Nn ψ _ (by exact hn.1))) hy1

end SubDatum

section Chi
variable {G : Type} [Group G] {N : ℕ}

def chiVal (χ : G →* Multiplicative (ZMod N)) (g : G) : ℕ := (Multiplicative.toAdd (χ g) : ZMod N).val

def chiCarry (χ : G →* Multiplicative (ZMod N)) (g h : G) : ℕ := (chiVal χ g + chiVal χ h) / N

def chiCorr (χ χ' : G →* Multiplicative (ZMod N)) (g : G) : ℕ := (chiVal χ g + chiVal χ' g) / N

def chiCocycle (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A) : G × G → A :=
  fun p => if N ≤ chiVal χ p.1 + chiVal χ p.2 then a else 0

variable [NeZero N]

theorem chiVal_lt (χ : G →* Multiplicative (ZMod N)) (g : G) : chiVal χ g < N := ZMod.val_lt _

theorem chiVal_one (χ : G →* Multiplicative (ZMod N)) : chiVal χ 1 = 0 := by
  simp [chiVal]

theorem chiVal_one_hom (g : G) : chiVal (1 : G →* Multiplicative (ZMod N)) g = 0 := by
  simp [chiVal]

theorem chiVal_mul (χ : G →* Multiplicative (ZMod N)) (g h : G) :
    chiVal χ (g * h) = (chiVal χ g + chiVal χ h) % N := by
  simp only [chiVal, map_mul, toAdd_mul, ZMod.val_add]

theorem chiVal_add_chiVal (χ : G →* Multiplicative (ZMod N)) (g h : G) :
    chiVal χ g + chiVal χ h = chiVal χ (g * h) + N * chiCarry χ g h := by
  rw [chiVal_mul, chiCarry]; exact (Nat.mod_add_div _ _).symm

theorem chiVal_mul_hom (χ χ' : G →* Multiplicative (ZMod N)) (g : G) :
    chiVal χ g + chiVal χ' g = chiVal (χ * χ') g + N * chiCorr χ χ' g := by
  simp only [chiVal, chiCorr, MonoidHom.mul_apply, toAdd_mul, ZMod.val_add]
  exact (Nat.mod_add_div _ _).symm

theorem chiCarry_eq_ite (χ : G →* Multiplicative (ZMod N)) (g h : G) :
    chiCarry χ g h = if N ≤ chiVal χ g + chiVal χ h then 1 else 0 := by
  have h1 := chiVal_lt χ g
  have h2 := chiVal_lt χ h
  have hN : 0 < N := Nat.pos_of_neZero N
  unfold chiCarry
  split_ifs with hle
  · apply Nat.div_eq_of_lt_le <;> omega
  · exact Nat.div_eq_of_lt (by omega)

theorem chiCocycle_apply (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A) (g h : G) :
    chiCocycle χ a (g, h) = (chiCarry χ g h : ℤ) • a := by
  simp only [chiCocycle, chiCarry_eq_ite]
  split_ifs <;> simp

theorem chiCocycle_one {A : Rep ℤ G} (a : A) : chiCocycle (1 : G →* Multiplicative (ZMod N)) a = 0 := by
  funext p
  have hN : 0 < N := Nat.pos_of_neZero N
  simp only [chiCocycle, chiVal_one_hom, add_zero, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem chiCocycle_mem_cocycles₂ (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A)
    (ha : ∀ g : G, A.ρ g a = a) : chiCocycle χ a ∈ cocycles₂ A := by
  rw [mem_cocycles₂_iff]
  intro g h j
  simp only [chiCocycle_apply, map_zsmul, ha, ← add_smul]
  congr 1
  have h1 := chiVal_add_chiVal χ g h
  have h2 := chiVal_add_chiVal χ (g * h) j
  have h3 := chiVal_add_chiVal χ h j
  have h4 := chiVal_add_chiVal χ g (h * j)
  rw [mul_assoc] at h2
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have key : (N : ℤ) * ((chiCarry χ (g * h) j : ℤ) + chiCarry χ g h) =
      (N : ℤ) * ((chiCarry χ h j : ℤ) + chiCarry χ g (h * j)) := by
    push_cast [Nat.cast_add, Nat.cast_mul] at h1 h2 h3 h4 ⊢
    zify at h1 h2 h3 h4
    linear_combination h3 + h4 - h1 - h2
  exact mul_left_cancel₀ hN key

theorem chiCocycle_mul_eq (χ χ' : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A)
    (ha : ∀ g : G, A.ρ g a = a) :
    chiCocycle (χ * χ') a = chiCocycle χ a + chiCocycle χ' a -
      (d₁₂ A).hom (fun g => (chiCorr χ χ' g : ℤ) • a) := by
  funext p
  obtain ⟨g, h⟩ := p
  simp only [Pi.sub_apply, Pi.add_apply, chiCocycle_apply, d₁₂_hom_apply, map_zsmul, ha]
  rw [← add_smul, ← sub_smul, ← add_smul, ← sub_smul]
  congr 1
  have h1 := chiVal_add_chiVal χ g h
  have h2 := chiVal_add_chiVal χ' g h
  have h3 := chiVal_add_chiVal (χ * χ') g h
  have h4 := chiVal_mul_hom χ χ' g
  have h5 := chiVal_mul_hom χ χ' h
  have h6 := chiVal_mul_hom χ χ' (g * h)
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have key : (N : ℤ) * (chiCarry (χ * χ') g h : ℤ) =
      (N : ℤ) * ((chiCarry χ g h : ℤ) + chiCarry χ' g h -
        ((chiCorr χ χ' h : ℤ) - chiCorr χ χ' (g * h) + chiCorr χ χ' g)) := by
    zify at h1 h2 h3 h4 h5 h6
    linear_combination h1 + h2 + h6 - h3 - h4 - h5
  exact mul_left_cancel₀ hN key

theorem H2π_chiCocycle_mul (χ χ' : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A)
    (ha : ∀ g : G, A.ρ g a = a) (h : chiCocycle (χ * χ') a ∈ cocycles₂ A)
    (h₁ : chiCocycle χ a ∈ cocycles₂ A) (h₂ : chiCocycle χ' a ∈ cocycles₂ A) :
    (H2π A).hom ⟨chiCocycle (χ * χ') a, h⟩ = (H2π A).hom ⟨chiCocycle χ a, h₁⟩ + (H2π A).hom ⟨chiCocycle χ' a, h₂⟩ := by
  rw [← map_add, H2π_eq_iff]
  refine ⟨-(fun g => (chiCorr χ χ' g : ℤ) • a), ?_⟩
  rw [map_neg]
  change _ = chiCocycle (χ * χ') a - (chiCocycle χ a + chiCocycle χ' a)
  rw [chiCocycle_mul_eq χ χ' a ha]
  abel

theorem H2π_chiCocycle_one {A : Rep ℤ G} (a : A) (h : chiCocycle (1 : G →* Multiplicative (ZMod N)) a ∈ cocycles₂ A) :
    (H2π A).hom ⟨chiCocycle (1 : G →* Multiplicative (ZMod N)) a, h⟩ = 0 := by
  rw [H2π_eq_zero_iff]
  refine ⟨0, ?_⟩
  rw [map_zero]
  change (0 : G × G → A) = chiCocycle 1 a
  rw [chiCocycle_one]

theorem H2π_chiCocycle_congr {χ χ' : G →* Multiplicative (ZMod N)} (hχ : χ = χ') {A : Rep ℤ G} (a : A)
    (h : chiCocycle χ a ∈ cocycles₂ A) (h' : chiCocycle χ' a ∈ cocycles₂ A) :
    (H2π A).hom ⟨chiCocycle χ a, h⟩ = (H2π A).hom ⟨chiCocycle χ' a, h'⟩ := by
  subst hχ; rfl

theorem H2π_chiCocycle_pow (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A)
    (ha : ∀ g : G, A.ρ g a = a) (i : ℕ) :
    (H2π A).hom ⟨chiCocycle (χ ^ i) a, chiCocycle_mem_cocycles₂ _ a ha⟩ =
      i • (H2π A).hom ⟨chiCocycle χ a, chiCocycle_mem_cocycles₂ _ a ha⟩ := by
  induction i with
  | zero =>
    rw [zero_smul]
    exact (H2π_chiCocycle_congr (pow_zero χ) a _ (chiCocycle_mem_cocycles₂ _ a ha)).trans
      (H2π_chiCocycle_one (N := N) a _)
  | succ i ih =>
    rw [succ_nsmul, ← ih, ← H2π_chiCocycle_mul (χ ^ i) χ a ha (chiCocycle_mem_cocycles₂ _ a ha)]
    exact H2π_chiCocycle_congr (pow_succ χ i) a _ _

end Chi

section ChiOf
variable {G : Type} [Group G] {N : ℕ} [NeZero N]

theorem cyclicLog_spec {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (g : Q) : t ^ cyclicLog t ht htfin g = g := by
  unfold cyclicLog
  have := pow_finEquivZPowers_symm_apply htfin ⟨g, ht g⟩
  simpa using this

theorem cyclicLog_lt {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (g : Q) : cyclicLog t ht htfin g < orderOf t :=
  ((finEquivZPowers htfin).symm ⟨g, ht g⟩).isLt

theorem cyclicLog_mul_modEq {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (g h : Q) : cyclicLog t ht htfin (g * h) ≡ cyclicLog t ht htfin g + cyclicLog t ht htfin h [MOD orderOf t] := by
  rw [← pow_eq_pow_iff_modEq, pow_add, cyclicLog_spec, cyclicLog_spec, cyclicLog_spec]

theorem cyclicLog_one {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t) :
    cyclicLog t ht htfin 1 = 0 := by
  have h2 := cyclicLog_lt t ht htfin 1
  have h1 : t ^ cyclicLog t ht htfin 1 = t ^ 0 := by rw [pow_zero]; exact cyclicLog_spec t ht htfin 1
  rw [pow_eq_pow_iff_modEq, Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt h2] at h1
  exact h1

noncomputable def chiOf (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) : G →* Multiplicative (ZMod N) where
  toFun g := Multiplicative.ofAdd (((N / orderOf t) * cyclicLog t ht htfin (QuotientGroup.mk g) : ℕ) : ZMod N)
  map_one' := by
    simp only [QuotientGroup.mk_one, cyclicLog_one, mul_zero, Nat.cast_zero, ofAdd_zero]
  map_mul' g h := by
    rw [← ofAdd_add, ← Nat.cast_add, QuotientGroup.mk_mul]
    congr 1
    rw [ZMod.natCast_eq_natCast_iff, ← mul_add]
    have := (cyclicLog_mul_modEq t ht htfin (QuotientGroup.mk g) (QuotientGroup.mk h)).mul_left' (N / orderOf t)
    rwa [Nat.div_mul_cancel hN] at this

theorem chiVal_chiOf (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g : G) :
    chiVal (chiOf S t ht htfin hN) g = (N / orderOf t) * cyclicLog t ht htfin (QuotientGroup.mk g) := by
  simp only [chiVal, chiOf, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  calc (N / orderOf t) * cyclicLog t ht htfin (QuotientGroup.mk g)
      < (N / orderOf t) * orderOf t :=
        (Nat.mul_lt_mul_left (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hN) htfin.orderOf_pos)).mpr
          (cyclicLog_lt t ht htfin _)
    _ = N := Nat.div_mul_cancel hN

theorem chiOf_apply_mk_eq (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g : G) (i : ℕ) (hi : (QuotientGroup.mk g : G ⧸ S) = t ^ i) :
    chiOf S t ht htfin hN g = Multiplicative.ofAdd (((N / orderOf t) * i : ℕ) : ZMod N) := by
  simp only [chiOf, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  rw [ZMod.natCast_eq_natCast_iff]
  have h1 : t ^ cyclicLog t ht htfin (QuotientGroup.mk g) = t ^ i := by rw [cyclicLog_spec]; exact hi
  rw [pow_eq_pow_iff_modEq] at h1
  have := h1.mul_left' (N / orderOf t)
  rwa [Nat.div_mul_cancel hN] at this

theorem le_chiVal_add_iff (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g h : G) :
    N ≤ chiVal (chiOf S t ht htfin hN) g + chiVal (chiOf S t ht htfin hN) h ↔
      orderOf t ≤ cyclicLog t ht htfin (QuotientGroup.mk g) + cyclicLog t ht htfin (QuotientGroup.mk h) := by
  rw [chiVal_chiOf, chiVal_chiOf, ← mul_add]
  have hpos : 0 < N / orderOf t := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hN) htfin.orderOf_pos
  constructor
  · intro hle
    by_contra hlt
    push Not at hlt
    have := (Nat.mul_lt_mul_left hpos).mpr hlt
    rw [Nat.div_mul_cancel hN] at this
    omega
  · intro hle
    calc N = (N / orderOf t) * orderOf t := (Nat.div_mul_cancel hN).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hle

theorem inf_H2π_carryFun_eq (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) {A : Rep ℤ G} (x : A.quotientToInvariants S)
    (hc : carryFun t ht htfin x ∈ cocycles₂ (A.quotientToInvariants S))
    (hc' : chiCocycle (chiOf S t ht htfin hN) (x.1 : A) ∈ cocycles₂ A) :
    ((infNatTrans ℤ S 2).app A).hom ((H2π (A.quotientToInvariants S)).hom ⟨carryFun t ht htfin x, hc⟩) =
      (H2π A).hom ⟨chiCocycle (chiOf S t ht htfin hN) (x.1 : A), hc'⟩ := by
  rw [infNatTrans_app]
  change (H2π _ ≫ map _ _ 2).hom _ = _
  rw [H2π_comp_map]
  change (H2π A).hom (mapCocycles₂ _ _ _) = _
  congr 1
  apply cocycles₂_ext
  intro g h
  rw [coe_mapCocycles₂]
  change (carryFun t ht htfin x (QuotientGroup.mk g, QuotientGroup.mk h)).1 = chiCocycle (chiOf S t ht htfin hN) x.1 (g, h)
  simp only [carryFun, chiCocycle, le_chiVal_add_iff]
  split_ifs <;> rfl

end ChiOf

section P4
variable {G : Type} [Group G] {N : ℕ} [NeZero N]

theorem chiOf_eq_one_of_mem (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g : G) (hg : g ∈ S) : chiOf S t ht htfin hN g = 1 := by
  have : (QuotientGroup.mk g : G ⧸ S) = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  simp only [chiOf, MonoidHom.coe_mk, OneHom.coe_mk, this, cyclicLog_one, mul_zero, Nat.cast_zero, ofAdd_zero]

theorem exists_eq_natCast_div_mul {d : ℕ} (hd : d ∣ N) (hd0 : 0 < d) (w : ZMod N) (hw : d • w = 0) :
    ∃ i : ℕ, w = ((N / d * i : ℕ) : ZMod N) := by
  have h1 : ((d * w.val : ℕ) : ZMod N) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, hw]
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨e, he⟩ := hd
  have hNd : N / d = e := by rw [he, Nat.mul_div_cancel_left _ hd0]
  obtain ⟨k, hk⟩ := h1
  have h2 : d * e ∣ d * w.val := ⟨k, by rw [hk, he]⟩
  obtain ⟨i, hi⟩ := Nat.dvd_of_mul_dvd_mul_left hd0 h2
  refine ⟨i, ?_⟩
  rw [hNd, ← hi, ZMod.natCast_zmod_val]

variable [Finite G]

theorem exists_chiOf_eq (χ : G →* Multiplicative (ZMod N)) :
    ∃ (t : G ⧸ χ.ker) (ht : ∀ g : G ⧸ χ.ker, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
      (hN : orderOf t ∣ N), χ = chiOf χ.ker t ht htfin hN := by
  classical
  set d := Nat.card (G ⧸ χ.ker) with hd
  have hd0 : 0 < d := Nat.card_pos
  have hN0 : N ≠ 0 := NeZero.ne N

  have hdN : d ∣ N := by
    have h1 : d = Nat.card χ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv
    rw [h1]
    have := Subgroup.card_subgroup_dvd_card χ.range
    rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod N)), Fintype.card_multiplicative, ZMod.card] at this

  have hval : ∀ g : G, ∃ i : ℕ, χ g = Multiplicative.ofAdd ((N / d * i : ℕ) : ZMod N) := by
    intro g
    have hgd : χ g ^ d = 1 := by
      rw [← map_pow, ← QuotientGroup.kerLift_mk, QuotientGroup.mk_pow, pow_card_eq_one', map_one]
    obtain ⟨i, hi⟩ := exists_eq_natCast_div_mul hdN hd0 (Multiplicative.toAdd (χ g))
      (by rw [← toAdd_pow, hgd, toAdd_one])
    exact ⟨i, by rw [← hi, ofAdd_toAdd]⟩

  set z : Multiplicative (ZMod N) := Multiplicative.ofAdd ((N / d : ℕ) : ZMod N) with hz
  have hzord : orderOf z = d := by
    rw [hz, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_coe _ hN0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdN),
      Nat.div_div_self hdN hN0]
  have hrange : χ.range = Subgroup.zpowers z := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨g, rfl⟩
      obtain ⟨i, hi⟩ := hval g
      refine ⟨(i : ℤ), ?_⟩
      change z ^ (i : ℤ) = χ g
      rw [zpow_natCast, hi, hz, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul, mul_comm]
    · rw [Nat.card_zpowers, hzord]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv).le
  have hzmem : z ∈ χ.range := by rw [hrange]; exact Subgroup.mem_zpowers z
  obtain ⟨g₁, hg₁⟩ := hzmem

  set t : G ⧸ χ.ker := QuotientGroup.mk g₁ with htdef
  have htord : orderOf t = d := by
    rw [← orderOf_injective (QuotientGroup.kerLift χ) (QuotientGroup.kerLift_injective χ) t, htdef,
      QuotientGroup.kerLift_mk, hg₁, hzord]
  have htop : Subgroup.zpowers t = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, htord]
  have ht : ∀ g : G ⧸ χ.ker, g ∈ Subgroup.zpowers t := fun g => by rw [htop]; exact Subgroup.mem_top g
  have htfin : IsOfFinOrder t := isOfFinOrder_of_finite t
  refine ⟨t, ht, htfin, htord ▸ hdN, ?_⟩
  ext g
  have hj := cyclicLog_spec t ht htfin (QuotientGroup.mk g)
  set j := cyclicLog t ht htfin (QuotientGroup.mk g)
  rw [chiOf_apply_mk_eq χ.ker t ht htfin (htord ▸ hdN) g j hj.symm, htord]

  have hmem : (g₁ ^ j)⁻¹ * g ∈ χ.ker := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_pow, ← htdef, hj]
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hg₁, inv_mul_eq_one] at hmem
  rw [← hmem, hz, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul, mul_comm]

end P4

section ResChi
variable {H : Type} [Group H] {N : ℕ} [NeZero N]

theorem res_H2π_chiCocycle (T : Subgroup H) (χ : H →* Multiplicative (ZMod N)) {A : Rep ℤ H} (a : A)
    (h : chiCocycle χ a ∈ cocycles₂ A) (h' : chiCocycle (χ.comp T.subtype) a ∈ cocycles₂ (Rep.res T.subtype A)) :
    (map T.subtype (𝟙 (Rep.res T.subtype A)) 2).hom ((H2π A).hom ⟨chiCocycle χ a, h⟩) =
      (H2π (Rep.res T.subtype A)).hom ⟨chiCocycle (χ.comp T.subtype) a, h'⟩ := by
  change (H2π _ ≫ map _ _ 2).hom _ = _
  rw [H2π_comp_map]
  change (H2π (Rep.res T.subtype A)).hom (mapCocycles₂ _ _ _) = _
  congr 1

theorem chi_ext_of_gen {Q : Type} [Group Q] (Nm : Subgroup Q) [Nm.Normal] (t : Q)
    (hgen : ∀ c : Q ⧸ Nm, c ∈ Subgroup.zpowers (QuotientGroup.mk t))
    (χ₁ χ₂ : Q →* Multiplicative (ZMod N)) (h₁ : ∀ n ∈ Nm, χ₁ n = 1) (h₂ : ∀ n ∈ Nm, χ₂ n = 1)
    (ht : χ₁ t = χ₂ t) : χ₁ = χ₂ := by
  ext g
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hgen (QuotientGroup.mk g))
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hi
  have e1 : χ₁ g = χ₁ t ^ i := by
    have := h₁ _ hi
    rw [map_mul, map_inv, map_zpow, inv_mul_eq_one] at this
    exact this.symm
  have e2 : χ₂ g = χ₂ t ^ i := by
    have := h₂ _ hi
    rw [map_mul, map_inv, map_zpow, inv_mul_eq_one] at this
    exact this.symm
  rw [e1, e2, ht]

theorem chiOf_apply_of_mem {G : Type} [Group G] (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g : G) (hg : g ∈ S) : chiOf S t ht htfin hN g = 1 :=
  chiOf_eq_one_of_mem S t ht htfin hN g hg

end ResChi

section MapLemmas
universe u
variable {k : Type u} [CommRing k]

theorem map_map_apply {G₁ G₂ G₃ : Type u} [Group G₁] [Group G₂] [Group G₃]
    {A : Rep k G₃} {B : Rep k G₂} {C : Rep k G₁} (f : G₂ →* G₃) (g : G₁ →* G₂)
    (φ : Rep.res f A ⟶ B) (ψ : Rep.res g B ⟶ C) (n : ℕ) (x : groupCohomology A n) :
    (map g ψ n).hom ((map f φ n).hom x) = (map (f.comp g) ((Rep.resFunctor g).map φ ≫ ψ) n).hom x := by
  rw [map_comp]
  rfl

theorem map_congr_apply {G₁ G₃ : Type u} [Group G₁] [Group G₃] {A : Rep k G₃} {C : Rep k G₁}
    (f₁ f₂ : G₁ →* G₃) (hf : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ C) (φ₂ : Rep.res f₂ A ⟶ C)
    (h : ∀ x : A, φ₁.hom x = φ₂.hom x) (n : ℕ) (x : groupCohomology A n) :
    (map f₁ φ₁ n).hom x = (map f₂ φ₂ n).hom x := by
  subst hf
  have : φ₁ = φ₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext h))
  subst this
  rfl

end MapLemmas

section Probe
example {H : Type} [Group H] (T : Subgroup H) (Mu : Type) [CommGroup Mu] [MulDistribMulAction H Mu] :
    Rep.ofMulDistribMulAction (↥T) Mu = Rep.res T.subtype (Rep.ofMulDistribMulAction H Mu) := rfl
end Probe

section IotaD
variable {q : ℕ} [Fact q.Prime]
    {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
    {G : Type} [Group G] [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ]
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} {hLM : L ≤ M}
    {H : Type} [Group H] [MulSemiringAction H M] [MulDistribMulAction H (↥M)ˣ]
    {NL : Subgroup H} [NL.Normal] {e : G ≃* H ⧸ NL}

noncomputable def iotaD (hcompat : ∀ (g : G) (v : (↥L)ˣ), ((g • v : (↥L)ˣ) : L) = g • (v : L))
    (hcompatM : ∀ (h : H) (v : (↥M)ˣ), ((h • v : (↥M)ˣ) : M) = h • (v : M))
    (hsmul : ∀ (g : G) (h : H), (QuotientGroup.mk h : H ⧸ NL) = e g →
      ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q)) :
    Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶
      Rep.ofMulDistribMulAction H (↥M)ˣ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (MonoidHom.toAdditive (Units.map (IntermediateField.inclusion hLM).toRingHom.toMonoidHom)).toIntLinearMap (fun h v => by
      change Additive.ofMul (Units.map (IntermediateField.inclusion hLM).toRingHom.toMonoidHom (Additive.toMul
          ((Rep.ofMulDistribMulAction G (↥L)ˣ).ρ (e.symm (QuotientGroup.mk h)) v))) =
        (Rep.ofMulDistribMulAction H (↥M)ˣ).ρ h
          (Additive.ofMul (Units.map (IntermediateField.inclusion hLM).toRingHom.toMonoidHom (Additive.toMul v)))
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
      congr 1
      apply Units.ext
      change (IntermediateField.inclusion hLM)
          (((e.symm (QuotientGroup.mk h)) • Additive.toMul (α := (↥L)ˣ) v : (↥L)ˣ) : L) =
        ((h • Units.map (IntermediateField.inclusion hLM).toRingHom.toMonoidHom (Additive.toMul (α := (↥L)ˣ) v) : (↥M)ˣ) : M)
      rw [hcompat, hcompatM, Units.coe_map]
      apply Subtype.ext
      exact hsmul (e.symm (QuotientGroup.mk h)) h (by rw [MulEquiv.apply_symm_apply]) _))

theorem iotaD_val (hcompat : ∀ (g : G) (v : (↥L)ˣ), ((g • v : (↥L)ˣ) : L) = g • (v : L))
    (hcompatM : ∀ (h : H) (v : (↥M)ˣ), ((h • v : (↥M)ˣ) : M) = h • (v : M))
    (hsmul : ∀ (g : G) (h : H), (QuotientGroup.mk h : H ⧸ NL) = e g →
      ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q))
    (v : (↥L)ˣ) :
    (((Additive.toMul ((iotaD hcompat hcompatM hsmul).hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) =
      ((v : L) : PadicAlgCl q) := rfl

end IotaD

section QTI

theorem coe_qti_ρ_mk {H : Type} [Group H] {Mu : Type} [CommGroup Mu] [MulDistribMulAction H Mu]
    (S : Subgroup H) [S.Normal] (g : H) (b : (Rep.ofMulDistribMulAction H Mu).quotientToInvariants S) :
    ((((Rep.ofMulDistribMulAction H Mu).quotientToInvariants S).ρ (QuotientGroup.mk g) b).1 : Additive Mu) =
      Additive.ofMul (g • Additive.toMul (α := Mu) b.1) := by
  change ((Representation.ofQuotient ((Rep.ofMulDistribMulAction H Mu).ρ.toInvariants S) S (g : H ⧸ S) b).1 : Additive Mu) = _
  rw [Representation.ofQuotient_coe_apply]
  rfl

theorem carry_mem_of_fixed {H : Type} [Group H] {Mu : Type} [CommGroup Mu] [MulDistribMulAction H Mu]
    (S : Subgroup H) [S.Normal] (g : H) (ht : ∀ c : H ⧸ S, c ∈ Subgroup.zpowers (QuotientGroup.mk' S g))
    (htfin : IsOfFinOrder (QuotientGroup.mk' S g)) (m : Mu) (hm : ∀ h : H, h • m = m)
    (hmS : (Additive.ofMul m : Rep.ofMulDistribMulAction H Mu) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H Mu).ρ.comp S.subtype)) :
    carryFun (QuotientGroup.mk' S g) ht htfin (A := (Rep.ofMulDistribMulAction H Mu).quotientToInvariants S)
      ⟨Additive.ofMul m, hmS⟩ ∈ cocycles₂ ((Rep.ofMulDistribMulAction H Mu).quotientToInvariants S) :=
  groupCohomology.carryFun_mem_cocycles2 _ ht htfin _ (Subtype.ext ((coe_qti_ρ_mk S g _).trans (congrArg Additive.ofMul (hm g))))

end QTI

section Numerics
theorem div_mul_helper (N a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hN : a * b * c ∣ N) :
    N / (a * b * c) * b = N / (a * c) := by
  obtain ⟨r, hr⟩ := hN
  rw [hr, Nat.mul_div_cancel_left _ (by positivity), show a * b * c * r = (a * c) * (b * r) by ring,
    Nat.mul_div_cancel_left _ (by positivity), mul_comm]

theorem div_helper2 (N a c : ℕ) (ha : 0 < a) (hc : 0 < c) (hN : a * c ∣ N) :
    a * (N / (a * c)) = N / c := by
  obtain ⟨r, hr⟩ := hN
  rw [hr, Nat.mul_div_cancel_left _ (by positivity), show a * c * r = c * (a * r) by ring,
    Nat.mul_div_cancel_left _ hc]
end Numerics

section MainThm

scoped instance faithfulSMul_subgroup' {G : Type} [Group G] {X : Type} [MulAction G X] [FaithfulSMul G X] (T : Subgroup G) :
    FaithfulSMul (↥T) X :=
  ⟨fun {a b} h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := X) h)⟩

theorem orderOf_eq_card_quot {H : Type} [Group H] (Nm : Subgroup H) [Nm.Normal] (t : H ⧸ Nm)
    (ht : ∀ c : H ⧸ Nm, c ∈ Subgroup.zpowers t) : orderOf t = Nat.card (H ⧸ Nm) := by
  have htop : Subgroup.zpowers t = ⊤ := by rw [eq_top_iff]; intro c _; exact ht c
  rw [← Nat.card_zpowers, htop, Subgroup.card_top]

theorem main (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : IsLocalFundamentalClass q L G K u)
    (S : Subgroup G) (KS : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] KS] (hKS : IsBase q L (↥S) KS) :
    IsLocalFundamentalClass q L (↥S) KS
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom u) := by
  classical

  obtain ⟨M, _i1, hLM, H, _i2, _i3, _i4, _i5, _i6, NL, Nn, _i7, _i8, e, φ, π, hHq, hcompM, hbase, hlayer, hsmul, hcardq, hzp,
    hfrob, hπH, hπK, hπ1, hπmax⟩ :=
    ExtCitation.LocalLevel.exists_overlayer_unramified_level q L G hG hcompat K hK.le hK.mem_iff (Nat.card G) Nat.card_pos
  have d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π :=
    ⟨hHq, hcompM, hbase, hlayer, hsmul, hcardq, hzp, hfrob, hπH, hπK, hπ1, hπmax⟩
  have hKSM : KS ≤ M := hKS.le.trans hLM
  have hKM : K ≤ M := hK.le.trans hLM

  obtain ⟨ψ, π', hgen, hfrobψ, hπ'S, hπ'1, hπ'max⟩ :=
    ExtCitation.LocalLevel.exists_frobenius_uniformiser_inf_level q M H hHq hcompM (HS S NL e) KS hKSM
      (mem_KS_iff q L G K S KS hKS d) Nn π hπH hπ1 hπmax
  obtain ⟨ee, ff, hee, hff, heff, hnorm, hψφ⟩ :=
    ExtCitation.LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow q M H hHq hcompM K hKM hbase (HS S NL e) KS hKSM
      (mem_KS_iff q L G K S KS hKS d) Nn φ hfrob π hπH hπ1 hπmax ψ hfrobψ π' hπ'S hπ'1 hπ'max

  have hsS : 0 < Nat.card S := Nat.card_pos
  have hidxS : (HS S NL e).index = S.index := Subgroup.index_comap_of_surjective _ (proj_surjective NL e)
  have hn : Nat.card G = ee * ff * Nat.card S := by
    rw [← Subgroup.card_mul_index S, ← hidxS, ← heff]; ring
  have hGH : Nat.card G ∣ Nat.card H := by rw [← hcardq]; exact Subgroup.card_quotient_dvd_card Nn
  have hfin0 : IsOfFinOrder (QuotientGroup.mk' Nn φ) := isOfFinOrder_of_finite _
  have hordφ : orderOf (QuotientGroup.mk' Nn φ) = Nat.card G := by rw [orderOf_eq_card_quot Nn _ hzp, hcardq]
  have htfin : IsOfFinOrder (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) := isOfFinOrder_of_finite _
  have hordt : orderOf (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) = ee * Nat.card S := by
    rw [orderOf_mk_subgroupOf]
    change orderOf (QuotientGroup.mk' Nn (ψ : H)) = _
    rw [hψφ, map_pow, orderOf_pow_of_dvd hff.ne' (by rw [hordφ, hn]; exact ⟨ee * Nat.card S, by ring⟩), hordφ, hn,
      show ee * ff * Nat.card S = ff * (ee * Nat.card S) by ring, Nat.mul_div_cancel_left _ hff]
  haveI hNnS : (NnS S NL e Nn ψ (Nat.card S)).Normal := normal_NnS S NL e Nn ψ _ hgen
  have hidx : (NnS S NL e Nn ψ (Nat.card S)).index = Nat.card S :=
    index_NnS S NL e Nn ψ _ htfin hgen hsS.ne' (by rw [hordt]; exact Dvd.intro_left ee rfl)
  have dS := subDatum q L G K S KS hKS d ψ π' hgen hfrobψ hπ'S hπ'1 hπ'max hidx

  refine ExtCitation.LocalLevel.isLocalFundamentalClass_of_pin q L (↥S) (fun g x => hG g x) (fun g v => hcompat g v) KS hKS dS _ ?_
  intro ιS hιS hfinS hcS

  haveI : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
  have hHSH : Nat.card (↥(HS S NL e)) ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
  have hN₀ : orderOf (QuotientGroup.mk' Nn φ) ∣ Nat.card H := by rw [hordφ]; exact hGH
  have hN₁ : orderOf (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) ∣ Nat.card H := by
    rw [orderOf_eq_card_quot _ _ hgen]
    exact (Subgroup.card_quotient_dvd_card _).trans hHSH
  have hordS : orderOf (QuotientGroup.mk' (NnS S NL e Nn ψ (Nat.card S)) ψ) = Nat.card S := by rw [orderOf_eq_card_quot _ _ dS.mem_zpowers, dS.card_quotient]
  have hNS : orderOf (QuotientGroup.mk' (NnS S NL e Nn ψ (Nat.card S)) ψ) ∣ Nat.card H := by
    rw [orderOf_eq_card_quot _ _ dS.mem_zpowers]
    exact (Subgroup.card_quotient_dvd_card _).trans hHSH
  have heS : ee * Nat.card S ∣ Nat.card H := by rw [← hordt]; exact hN₁

  have hρπ : ∀ g : H, (Rep.ofMulDistribMulAction H (↥M)ˣ).ρ g (Additive.ofMul π) = Additive.ofMul π := fun g => by
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply]; exact congrArg Additive.ofMul (hπH g)
  have hπNn : (Additive.ofMul π : (Rep.ofMulDistribMulAction H (↥M)ˣ)) ∈ Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp Nn.subtype) := fun n => hρπ n
  have hc0 := carry_mem_of_fixed Nn φ hzp hfin0 π hπH hπNn
  have hud := hu M hLM H NL Nn e φ π d (iotaD hcompat hcompM hsmul) (iotaD_val hcompat hcompM hsmul) hfin0 hc0
  have step1 : ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
      ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin0 d.piInv, hc0⟩) =
      (H2π (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom ⟨chiCocycle (chiOf Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN₀) (Additive.ofMul π),
        chiCocycle_mem_cocycles₂ _ _ hρπ⟩ :=
    inf_H2π_carryFun_eq (A := (Rep.ofMulDistribMulAction H (↥M)ˣ)) Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN₀ d.piInv hc0 _

  have hρπS : ∀ g : ↥(HS S NL e), (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).ρ g (Additive.ofMul π) = Additive.ofMul π := fun g => hρπ g
  have step2 := res_H2π_chiCocycle (HS S NL e) (chiOf Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN₀) (A := (Rep.ofMulDistribMulAction H (↥M)ˣ)) (Additive.ofMul π)
    (chiCocycle_mem_cocycles₂ _ _ hρπ) (chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπS)
  have hχ₁ : (chiOf Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN₀).comp (HS S NL e).subtype = chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁ := by
    apply chi_ext_of_gen (Nn.subgroupOf (HS S NL e)) ψ hgen
    · intro n hn; exact chiOf_eq_one_of_mem Nn _ hzp hfin0 hN₀ (n : H) hn
    · intro n hn; exact chiOf_eq_one_of_mem (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁ n hn
    · change chiOf Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN₀ (ψ : H) = chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁ ψ
      rw [chiOf_apply_mk_eq Nn _ hzp hfin0 hN₀ (ψ : H) ff (by rw [← map_pow]; exact hψφ),
        chiOf_apply_mk_eq (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁ ψ 1 (by rw [pow_one]; rfl), mul_one, hordφ, hordt, hn,
        div_mul_helper _ _ _ _ hee hff hsS (hn ▸ hGH)]
  have step3 : (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle ((chiOf Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN₀).comp (HS S NL e).subtype)
      (Additive.ofMul π), chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπS⟩ =
      (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle (chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁) (Additive.ofMul π), chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπS⟩ :=
    H2π_chiCocycle_congr hχ₁ _ _ _

  have hπNn' : (Additive.ofMul π : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) ∈ Representation.invariants ((Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).ρ.comp (Nn.subgroupOf (HS S NL e)).subtype) := fun n => hρπS n
  have hcπ := carry_mem_of_fixed (Nn.subgroupOf (HS S NL e)) ψ hgen htfin π (fun g : ↥(HS S NL e) => hπH g) hπNn'
  have step4 : (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle (chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁) (Additive.ofMul π),
      chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπS⟩ =
      ((infNatTrans ℤ (Nn.subgroupOf (HS S NL e)) 2).app (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ((H2π ((Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e)))).hom
        ⟨carryFun (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))) (⟨Additive.ofMul π, hπNn'⟩ : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))), hcπ⟩) :=
    (inf_H2π_carryFun_eq (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁ (⟨Additive.ofMul π, hπNn'⟩ : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))) hcπ _).symm
  have hρπ'S : ∀ g : ↥(HS S NL e), (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).ρ g (Additive.ofMul π') = Additive.ofMul π' := fun g => by
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply]; exact congrArg Additive.ofMul (hπ'S g g.2)
  have hπ'Nn' : (Additive.ofMul π' : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) ∈ Representation.invariants ((Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).ρ.comp (Nn.subgroupOf (HS S NL e)).subtype) := fun n => hρπ'S n
  have hcπ' := carry_mem_of_fixed (Nn.subgroupOf (HS S NL e)) ψ hgen htfin π' (fun g : ↥(HS S NL e) => hπ'S g g.2) hπ'Nn'
  obtain ⟨inv', hinv'⟩ := ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun q M
    (↥(HS S NL e)) (fun g x => hHq g x) (fun g v => hcompM g v) (Nn.subgroupOf (HS S NL e)) ψ hgen htfin π' (fun g => hπ'S g g.2) hπ'1
    (fun y hy hy1 => hπ'max y (fun n hn => hy ⟨n, hn.2⟩ hn.1) hy1)
  have i1 := hinv' (⟨Additive.ofMul π, hπNn'⟩ : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))) (ee : ℤ) hcπ (by rw [zpow_natCast]; exact hnorm)
  have i2 := hinv' (⟨Additive.ofMul π', hπ'Nn'⟩ : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))) 1 hcπ' (by rw [zpow_one]; rfl)
  have step5 : (H2π ((Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e)))).hom
        ⟨carryFun (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))) (⟨Additive.ofMul π, hπNn'⟩ : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))), hcπ⟩ =
      ee • (H2π ((Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e)))).hom
        ⟨carryFun (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))) (⟨Additive.ofMul π', hπ'Nn'⟩ : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))), hcπ'⟩ := by
    apply inv'.injective
    rw [map_nsmul, i1, i2]
    simp
  have step6 : ((infNatTrans ℤ (Nn.subgroupOf (HS S NL e)) 2).app (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ((H2π ((Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e)))).hom
        ⟨carryFun (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))) (⟨Additive.ofMul π', hπ'Nn'⟩ : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))), hcπ'⟩) =
      (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle (chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁) (Additive.ofMul π'), chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπ'S⟩ :=
    inf_H2π_carryFun_eq (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁ (⟨Additive.ofMul π', hπ'Nn'⟩ : (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (Nn.subgroupOf (HS S NL e))) hcπ' _
  have step7 : ee • (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle (chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁) (Additive.ofMul π'),
      chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπ'S⟩ =
      (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle ((chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁) ^ ee) (Additive.ofMul π'), chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπ'S⟩ :=
    (H2π_chiCocycle_pow _ _ hρπ'S ee).symm
  have hχS : (chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁) ^ ee = chiOf (NnS S NL e Nn ψ (Nat.card S)) (QuotientGroup.mk' (NnS S NL e Nn ψ (Nat.card S)) ψ) dS.mem_zpowers hfinS hNS := by
    apply chi_ext_of_gen (Nn.subgroupOf (HS S NL e)) ψ hgen
    · intro n hn; rw [MonoidHom.pow_apply, chiOf_eq_one_of_mem (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁ n hn, one_pow]
    · intro n hn; exact chiOf_eq_one_of_mem (NnS S NL e Nn ψ (Nat.card S)) _ dS.mem_zpowers hfinS hNS n (subgroupOf_le_NnS S NL e Nn ψ _ hn)
    · rw [MonoidHom.pow_apply, chiOf_apply_mk_eq (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁ ψ 1 (by rw [pow_one]; rfl),
        chiOf_apply_mk_eq (NnS S NL e Nn ψ (Nat.card S)) _ dS.mem_zpowers hfinS hNS ψ 1 (by rw [pow_one]; rfl), mul_one, mul_one, hordt, hordS,
        ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, div_helper2 _ _ _ hee hsS heS]
  have step8 : (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle ((chiOf (Nn.subgroupOf (HS S NL e)) (QuotientGroup.mk' (Nn.subgroupOf (HS S NL e)) ψ) hgen htfin hN₁) ^ ee) (Additive.ofMul π'),
      chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπ'S⟩ =
      (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle (chiOf (NnS S NL e Nn ψ (Nat.card S)) (QuotientGroup.mk' (NnS S NL e Nn ψ (Nat.card S)) ψ) dS.mem_zpowers hfinS hNS) (Additive.ofMul π'),
        chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπ'S⟩ :=
    H2π_chiCocycle_congr hχS _ _ _
  have step9 : (H2π (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ⟨chiCocycle (chiOf (NnS S NL e Nn ψ (Nat.card S)) (QuotientGroup.mk' (NnS S NL e Nn ψ (Nat.card S)) ψ) dS.mem_zpowers hfinS hNS) (Additive.ofMul π'),
        chiCocycle_mem_cocycles₂ (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) _ _ hρπ'S⟩ =
      ((infNatTrans ℤ (NnS S NL e Nn ψ (Nat.card S)) 2).app (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom ((H2π ((Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ).quotientToInvariants (NnS S NL e Nn ψ (Nat.card S)))).hom
        ⟨carryFun (QuotientGroup.mk' (NnS S NL e Nn ψ (Nat.card S)) ψ) dS.mem_zpowers hfinS dS.piInv, hcS⟩) :=
    (inf_H2π_carryFun_eq (A := (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)) (NnS S NL e Nn ψ (Nat.card S)) _ dS.mem_zpowers hfinS hNS dS.piInv hcS _).symm

  have L1 := map_map_apply (k := ℤ) S.subtype ((eS S NL e).symm.toMonoidHom.comp (QuotientGroup.mk' (NL.subgroupOf (HS S NL e)))) (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) ιS 2 u
  have L2 := map_map_apply (k := ℤ) (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (HS S NL e).subtype (iotaD hcompat hcompM hsmul) (𝟙 (Rep.res (HS S NL e).subtype (Rep.ofMulDistribMulAction H (↥M)ˣ))) 2 u
  have hF : S.subtype.comp ((eS S NL e).symm.toMonoidHom.comp (QuotientGroup.mk' (NL.subgroupOf (HS S NL e)))) = (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)).comp (HS S NL e).subtype := by
    ext h
    change (((eS S NL e).symm (QuotientGroup.mk h) : ↥S) : G) = e.symm (QuotientGroup.mk (h : H))
    rw [(MulEquiv.symm_apply_eq (eS S NL e)).2 (eS_projS S NL e h).symm]
    rfl
  have L3 := map_congr_apply (k := ℤ) _ _ hF ((Rep.resFunctor ((eS S NL e).symm.toMonoidHom.comp (QuotientGroup.mk' (NL.subgroupOf (HS S NL e))))).map (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) ≫ ιS)
    ((Rep.resFunctor (HS S NL e).subtype).map (iotaD hcompat hcompM hsmul) ≫ 𝟙 (Rep.res (HS S NL e).subtype (Rep.ofMulDistribMulAction H (↥M)ˣ)))
    (fun x => by
      change ιS.hom x = (iotaD hcompat hcompM hsmul).hom x
      apply Additive.toMul.injective
      apply Units.ext
      apply Subtype.ext
      exact (hιS (Additive.toMul x)).trans (iotaD_val hcompat hcompM hsmul (Additive.toMul x)).symm) 2 u
  refine L1.trans (L3.trans (L2.symm.trans ?_))
  refine ((congrArg (fun y => (groupCohomology.map (HS S NL e).subtype (𝟙 (Rep.res (HS S NL e).subtype (Rep.ofMulDistribMulAction H (↥M)ˣ))) 2).hom y) hud).trans (congrArg (fun y => (groupCohomology.map (HS S NL e).subtype (𝟙 (Rep.res (HS S NL e).subtype (Rep.ofMulDistribMulAction H (↥M)ˣ))) 2).hom y) step1)).trans ?_
  refine (step2.trans (step3.trans step4)).trans ?_
  refine ((congrArg (fun y => ((infNatTrans ℤ (Nn.subgroupOf (HS S NL e)) 2).app (Rep.ofMulDistribMulAction (↥(HS S NL e)) (↥M)ˣ)).hom y) step5).trans (map_nsmul _ _ _)).trans ?_
  refine (congrArg (fun y => ee • y) step6).trans ?_
  exact step7.trans (step8.trans step9)

end MainThm

end ExtCitation.LocalLevel.ResFC
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.ExtCitation P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.ExtCitation.LocalLevel.ResFC"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.ExtCitation P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.ExtCitation.LocalLevel"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.ExtCitation"

theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : IsLocalFundamentalClass q L G K u)
    (S : Subgroup G) (KS : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] KS] (hKS : IsBase q L (↥S) KS) :
    IsLocalFundamentalClass q L (↥S) KS
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom u) :=
  ExtCitation.LocalLevel.ResFC.main q L G hG hcompat hsolv K hK u hu S KS hKS

end S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype
end P2MW
export P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype (solution)
